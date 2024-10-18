use criterion::{criterion_group, criterion_main, Criterion};
use std::hint::black_box;

mod utils;

static CBOR: &[u8] = include_bytes!("samples/sample.cbor");

fn bench_cbor(c: &mut Criterion) {
    c.bench_function("cbor_nom", {
        move |b| b.iter(|| black_box(nom::cbor(black_box(CBOR)).unwrap()))
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

fn i64_from_bytes(bytes: &[u8]) -> i64 {
    let mut b = [0; 8];
    bytes
        .iter()
        .rev()
        .zip(b.iter_mut().rev())
        .for_each(|(byte, b)| {
            *b = *byte;
        });

    i64::from_be_bytes(b)
}

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
    use crate::i64_from_bytes;
    use chumsky::prelude::*;

    type Error<'a> = EmptyErr;

    fn int_out(slice: &[u8]) -> i64 {
        if slice.len() == 1 {
            (slice[0] & 0b1_1111) as i64
        } else {
            i64_from_bytes(&slice[1..])
        }
    }

    pub fn cbor<'a>() -> impl Parser<'a, &'a [u8], CborZero<'a>, extra::Err<Error<'a>>> {
        recursive(|data| {
            let read_int = any()
                .try_map(|ctx, _| {
                    if ctx & 0b1_1111 < 28 {
                        Ok(ctx)
                    } else {
                        Err(Error::default())
                    }
                })
                .ignore_with_ctx(any().repeated().configure(|cfg, ctx| {
                    let info = *ctx & 0b1_1111;
                    let num = if info < 24 {
                        0
                    } else {
                        2usize.pow(info as u32 - 24)
                    };
                    cfg.exactly(num)
                }))
                .to_slice()
                .map(int_out);

            let uint = read_int.map(CborZero::Int);
            let nint = read_int.map(|i| CborZero::Int(-1 - i));
            // TODO: Handle indefinite lengths
            let bstr = read_int.ignore_with_ctx(
                any()
                    .repeated()
                    .configure(|cfg, ctx| cfg.exactly(*ctx as usize))
                    .to_slice()
                    .map(CborZero::Bytes),
            );

            let str = read_int.ignore_with_ctx(
                any()
                    .repeated()
                    .configure(|cfg, ctx| cfg.exactly(*ctx as usize))
                    .to_slice()
                    .map(|slice| CborZero::String(std::str::from_utf8(slice).unwrap())),
            );

            let array = read_int.ignore_with_ctx(
                data.clone()
                    .with_ctx(())
                    .repeated()
                    .configure(|cfg, ctx| cfg.exactly(*ctx as usize))
                    .collect::<Vec<_>>()
                    .map(CborZero::Array),
            );

            let map = read_int.ignore_with_ctx(
                data.clone()
                    .then(data.clone())
                    .with_ctx(())
                    .repeated()
                    .configure(|cfg, ctx| cfg.exactly(*ctx as usize))
                    .collect::<Vec<_>>()
                    .map(CborZero::Map),
            );

            let simple = |num: u8| {
                any().try_map(move |n, _| {
                    if n & 0b1_1111 == num {
                        Ok(())
                    } else {
                        Err(Error::default())
                    }
                })
            };

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

            let major = |num: u8| {
                any()
                    .try_map(move |n, _| {
                        if (n >> 5) == num {
                            Ok(())
                        } else {
                            Err(Error::default())
                        }
                    })
                    .rewind()
            };

            choice((
                major(0).ignore_then(uint),
                major(1).ignore_then(nint),
                major(2).ignore_then(bstr),
                major(3).ignore_then(str),
                major(4).ignore_then(array),
                major(5).ignore_then(map),
                major(6).ignore_then(todo()),
                major(7).ignore_then(float_simple),
            ))
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
