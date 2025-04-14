use criterion::{black_box, criterion_group, criterion_main, Criterion};

mod utils;

static CBOR: &[u8] = include_bytes!("samples/sample.cbor");

fn bench_cbor(c: &mut Criterion) {
    c.bench_function("cbor_nom", {
        move |b| b.iter(|| black_box(nom::cbor(black_box(CBOR)).unwrap()))
    });

    c.bench_function("cbor_nom8", {
        move |b| b.iter(|| black_box(nom8::cbor(black_box(CBOR)).unwrap()))
    });

    // c.bench_function("cbor_winnow", {
    //     move |b| b.iter(|| black_box(winnow::cbor(black_box(JSON)).unwrap()))
    // });

    c.bench_function("cbor_chumsky_zero_copy", {
        use ::chumsky::prelude::*;
        let cbor = chumsky_zero_copy::cbor();
        move |b| {
            b.iter(|| {
                black_box(cbor.parse(black_box(CBOR)))
                    .into_result()
                    .unwrap()
            })
        }
    });

    c.bench_function("cbor_chumsky_zero_copy_check", {
        use ::chumsky::prelude::*;
        let cbor = chumsky_zero_copy::cbor();
        move |b| {
            b.iter(|| {
                assert!(black_box(cbor.check(black_box(CBOR)))
                    .into_errors()
                    .is_empty())
            })
        }
    });

    c.bench_function("cbor_ciborium", {
        use ciborium::de::from_reader;
        use ciborium::value::Value;
        move |b| b.iter(|| black_box(from_reader::<Value, _>(black_box(CBOR)).unwrap()))
    });

    // c.bench_function("cbor_pom", {
    //     let cbor = pom::cbor();
    //     move |b| b.iter(|| black_box(cbor.parse(black_box(JSON)).unwrap()))
    // });

    // c.bench_function("cbor_pest", {
    //     let cbor = black_box(std::str::from_utf8(JSON).unwrap());
    //     move |b| b.iter(|| black_box(pest::parse(cbor).unwrap()))
    // });
}

criterion_group!(
    name = benches;
    config = utils::make_criterion();
    targets = bench_cbor
);

criterion_main!(benches);

#[derive(Debug, Clone, PartialEq)]
pub enum CborZero<'a> {
    Bool(bool),
    Null,
    Undef,
    Int(i64),
    Bytes(&'a [u8]),
    String(&'a str),
    Array(Vec<CborZero<'a>>),
    Map(Vec<(CborZero<'a>, CborZero<'a>)>),
    Tag(u64, Box<CborZero<'a>>),
    // Byte(u8)
    // HalfFloat(f16),
    SingleFloat(f32),
    DoubleFloat(f64),
}

mod chumsky_zero_copy {
    use super::CborZero;
    use chumsky::prelude::*;

    type Error<'a> = EmptyErr;

    pub fn cbor<'a>() -> impl Parser<'a, &'a [u8], CborZero<'a>, extra::Err<Error<'a>>> {
        recursive(|data| {
            let take = |n: u8| any().map(move |x| x % (1 << n));
            let int = |bytes| {
                empty()
                    .to(0u64)
                    .foldl(any().repeated().exactly(bytes), |a, x| (a << 8) | x as u64)
            };
            let read_uint = choice((
                take(5).filter(|x| *x <= 23).map(|x| x as u64),
                take(5).filter(|x| *x == 24).ignore_then(int(1)),
                take(5).filter(|x| *x == 25).ignore_then(int(2)),
                take(5).filter(|x| *x == 26).ignore_then(int(4)),
                take(5).filter(|x| *x == 27).ignore_then(int(8)),
            ));

            let uint = read_uint.map(|x| CborZero::Int(x.try_into().unwrap()));
            let nint = read_uint.map(|x| CborZero::Int(-1 - i64::try_from(x).unwrap()));

            let length = read_uint.map(|x| usize::try_from(x).unwrap());
            let bstr = length.ignore_with_ctx(
                any()
                    .repeated()
                    .configure(|cfg, ctx| cfg.exactly(*ctx))
                    .to_slice()
                    .map(CborZero::Bytes),
            );

            let str = length.ignore_with_ctx(
                any()
                    .repeated()
                    .configure(|cfg, ctx| cfg.exactly(*ctx))
                    .to_slice()
                    .map(|slice| CborZero::String(std::str::from_utf8(slice).unwrap())),
            );

            let array = length.ignore_with_ctx(
                data.clone()
                    .with_ctx(())
                    .repeated()
                    .configure(|cfg, ctx| cfg.exactly(*ctx))
                    .collect::<Vec<_>>()
                    .map(CborZero::Array),
            );

            let map = length.ignore_with_ctx(
                data.clone()
                    .then(data.clone())
                    .with_ctx(())
                    .repeated()
                    .configure(|cfg, ctx| cfg.exactly(*ctx))
                    .collect::<Vec<_>>()
                    .map(CborZero::Map),
            );

            let simple = |num: u8| any().filter(move |n| n % (1 << 5) == num);

            let float_simple = choice((
                simple(20).to(CborZero::Bool(false)),
                simple(21).to(CborZero::Bool(true)),
                simple(22).to(CborZero::Null),
                simple(23).to(CborZero::Undef),
                simple(26).ignore_then(
                    any()
                        .repeated()
                        .collect_exactly()
                        .map(f32::from_be_bytes)
                        .map(CborZero::SingleFloat),
                ),
                simple(27).ignore_then(
                    any()
                        .repeated()
                        .collect_exactly()
                        .map(f64::from_be_bytes)
                        .map(CborZero::DoubleFloat),
                ),
            ));

            recursive(|value| {
                let major =
                    |num: u8, bits: u8| any().rewind().filter(move |n| n >> (8 - bits) == num);

                let tag = major(6, 3)
                    .ignore_then(read_uint)
                    .then(value)
                    .map(|(tag, value)| CborZero::Tag(tag, Box::new(value)));

                choice((
                    major(0, 3).ignore_then(uint),
                    major(1, 3).ignore_then(nint),
                    major(2, 3).ignore_then(bstr),
                    major(3, 3).ignore_then(str),
                    major(4, 3).ignore_then(array),
                    major(5, 3).ignore_then(map),
                    major(6, 3).ignore_then(tag),
                    major(7, 3).ignore_then(float_simple),
                ))
            })
        })
    }
}

mod nom {
    use super::CborZero;
    use nom::{
        bits::{bits, bytes},
        branch::alt,
        bytes::complete::take as take_bytes,
        combinator::{map, value as to, verify},
        complete::{tag, take},
        multi::count,
        number::complete::{be_f32, be_f64},
        sequence::{pair, preceded},
        IResult,
    };

    fn integer(i: (&[u8], usize)) -> IResult<(&[u8], usize), u64> {
        alt((
            verify(take(5usize), |&v| v < 24),
            preceded(tag(24, 5usize), take(8usize)),
            preceded(tag(25, 5usize), take(16usize)),
            preceded(tag(26, 5usize), take(32usize)),
            preceded(tag(27, 5usize), take(64usize)),
        ))(i)
    }

    fn uint<'a>(i: &[u8]) -> IResult<&[u8], CborZero<'a>> {
        bits(preceded(
            tag(0, 3usize),
            map(integer, |v| CborZero::Int(v.try_into().unwrap())),
        ))(i)
    }

    fn nint<'a>(i: &[u8]) -> IResult<&[u8], CborZero<'a>> {
        bits(preceded(
            tag(1, 3usize),
            map(integer, |v| CborZero::Int(-1 - i64::try_from(v).unwrap())),
        ))(i)
    }

    fn bstr(i: &[u8]) -> IResult<&[u8], CborZero<'_>> {
        // TODO: Handle indefinite length
        let (i, length) = bits(preceded(tag(2, 3usize), integer))(i)?;
        let length = usize::try_from(length).unwrap();
        let (i, data) = take_bytes(length)(i)?;
        Ok((i, CborZero::Bytes(data)))
    }

    fn str(i: &[u8]) -> IResult<&[u8], CborZero<'_>> {
        // TODO: Handle indefinite length
        let (i, length) = bits(preceded(tag(3, 3usize), integer))(i)?;
        let length = usize::try_from(length).unwrap();
        let (i, data) = take_bytes(length)(i)?;
        Ok((i, CborZero::String(std::str::from_utf8(data).unwrap())))
    }

    fn array(i: &[u8]) -> IResult<&[u8], CborZero<'_>> {
        // TODO: Handle indefinite length
        let (i, length) = bits(preceded(tag(4, 3usize), integer))(i)?;
        let (i, data) = count(value, length as usize)(i)?;
        Ok((i, CborZero::Array(data)))
    }

    fn cbor_map(i: &[u8]) -> IResult<&[u8], CborZero<'_>> {
        // TODO: Handle indefinite length
        let (i, length) = bits(preceded(tag(5, 3usize), integer))(i)?;
        let (i, data) = count(pair(value, value), length as usize)(i)?;
        Ok((i, CborZero::Map(data)))
    }

    fn cbor_tag(i: &[u8]) -> IResult<&[u8], CborZero<'_>> {
        let (i, tag) = bits(preceded(tag(6, 3usize), integer))(i)?;
        let (i, value) = value(i)?;
        Ok((i, CborZero::Tag(tag, Box::new(value))))
    }

    fn float_simple(i: &[u8]) -> IResult<&[u8], CborZero<'_>> {
        bits(preceded(
            tag(7, 3usize),
            alt((
                to(CborZero::Bool(false), tag(20, 5usize)),
                to(CborZero::Bool(true), tag(21, 5usize)),
                to(CborZero::Null, tag(22, 5usize)),
                to(CborZero::Undef, tag(23, 5usize)),
                // preceded(tag(24, 5usize), ...), // u8
                // preceded(tag(25, 5usize), map(be_f16, |v| CborZero::HalfFloat(v))),
                preceded(
                    tag(26, 5usize),
                    map(bytes(be_f32::<_, nom::error::Error<&[u8]>>), |v| {
                        CborZero::SingleFloat(v)
                    }),
                ),
                preceded(
                    tag(27, 5usize),
                    map(bytes(be_f64::<_, nom::error::Error<&[u8]>>), |v| {
                        CborZero::DoubleFloat(v)
                    }),
                ),
            )),
        ))(i)
    }

    fn value(i: &[u8]) -> IResult<&[u8], CborZero<'_>> {
        alt((
            uint,
            nint,
            bstr,
            str,
            array,
            cbor_map,
            cbor_tag,
            float_simple,
        ))(i)
    }

    pub fn cbor(i: &[u8]) -> IResult<&[u8], CborZero<'_>> {
        value(i)
    }
}

mod nom8 {
    use super::CborZero;
    use nom8::{
        bits::{
            bits, bytes,
            complete::{tag, take},
        },
        branch::alt,
        bytes::complete::take as take_bytes,
        combinator::{map, value as to, verify},
        multi::count,
        number::complete::{be_f32, be_f64},
        sequence::{pair, preceded},
        IResult, Parser,
    };

    fn integer(i: (&[u8], usize)) -> IResult<(&[u8], usize), u64> {
        alt((
            verify(take(5usize), |&v| v < 24),
            preceded(tag(24, 5usize), take(8usize)),
            preceded(tag(25, 5usize), take(16usize)),
            preceded(tag(26, 5usize), take(32usize)),
            preceded(tag(27, 5usize), take(64usize)),
        ))
        .parse_complete(i)
    }

    fn uint<'a>(i: &[u8]) -> IResult<&[u8], CborZero<'a>> {
        bits(preceded(
            tag(0, 3usize),
            map(integer, |v| CborZero::Int(v.try_into().unwrap())),
        ))
        .parse_complete(i)
    }

    fn nint<'a>(i: &[u8]) -> IResult<&[u8], CborZero<'a>> {
        bits(preceded(
            tag(1, 3usize),
            map(integer, |v| CborZero::Int(-1 - i64::try_from(v).unwrap())),
        ))
        .parse_complete(i)
    }

    fn bstr(i: &[u8]) -> IResult<&[u8], CborZero<'_>> {
        // TODO: Handle indefinite length
        let (i, length) = bits(preceded(tag(2, 3usize), integer)).parse_complete(i)?;
        let length = usize::try_from(length).unwrap();
        let (i, data) = take_bytes(length).parse_complete(i)?;
        Ok((i, CborZero::Bytes(data)))
    }

    fn str(i: &[u8]) -> IResult<&[u8], CborZero<'_>> {
        // TODO: Handle indefinite length
        let (i, length) = bits(preceded(tag(3, 3usize), integer)).parse_complete(i)?;
        let length = usize::try_from(length).unwrap();
        let (i, data) = take_bytes(length).parse_complete(i)?;
        Ok((i, CborZero::String(std::str::from_utf8(data).unwrap())))
    }

    fn array(i: &[u8]) -> IResult<&[u8], CborZero<'_>> {
        // TODO: Handle indefinite length
        let (i, length) = bits(preceded(tag(4, 3usize), integer)).parse_complete(i)?;
        let (i, data) = count(value, length as usize).parse_complete(i)?;
        Ok((i, CborZero::Array(data)))
    }

    fn cbor_map(i: &[u8]) -> IResult<&[u8], CborZero<'_>> {
        // TODO: Handle indefinite length
        let (i, length) = bits(preceded(tag(5, 3usize), integer))(i)?;
        let (i, data) = count(pair(value, value), length as usize).parse_complete(i)?;
        Ok((i, CborZero::Map(data)))
    }

    fn cbor_tag(i: &[u8]) -> IResult<&[u8], CborZero<'_>> {
        let (i, tag) = bits(preceded(tag(6, 3usize), integer))(i)?;
        let (i, value) = value(i)?;
        Ok((i, CborZero::Tag(tag, Box::new(value))))
    }

    fn float_simple(i: &[u8]) -> IResult<&[u8], CborZero<'_>> {
        bits(preceded(
            tag(7, 3usize),
            alt((
                to(CborZero::Bool(false), tag(20, 5usize)),
                to(CborZero::Bool(true), tag(21, 5usize)),
                to(CborZero::Null, tag(22, 5usize)),
                to(CborZero::Undef, tag(23, 5usize)),
                // preceded(tag(24, 5usize), ...), // u8
                // preceded(tag(25, 5usize), map(be_f16, |v| CborZero::HalfFloat(v))),
                preceded(
                    tag(26, 5usize),
                    map(bytes(be_f32::<_, nom8::error::Error<&[u8]>>), |v| {
                        CborZero::SingleFloat(v)
                    }),
                ),
                preceded(
                    tag(27, 5usize),
                    map(bytes(be_f64::<_, nom8::error::Error<&[u8]>>), |v| {
                        CborZero::DoubleFloat(v)
                    }),
                ),
            )),
        ))
        .parse_complete(i)
    }

    fn value(i: &[u8]) -> IResult<&[u8], CborZero<'_>> {
        alt((
            uint,
            nint,
            bstr,
            str,
            array,
            cbor_map,
            cbor_tag,
            float_simple,
        ))
        .parse_complete(i)
    }

    pub fn cbor(i: &[u8]) -> IResult<&[u8], CborZero<'_>> {
        value(i)
    }
}
