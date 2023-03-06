use std::hint::black_box;
use criterion::{Criterion, criterion_group, criterion_main};

mod utils;

static CBOR: &'static [u8] = include_bytes!("samples/sample.cbor");

fn bench_cbor(c: &mut Criterion) {
    // c.bench_function("cbor_nom", {
    //     move |b| b.iter(|| black_box(nom::cbor(black_box(CBOR)).unwrap()))
    // });

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

    c.bench_function("cbor_serde_cbor", {
        use serde_cbor::{from_slice, Value};
        move |b| b.iter(|| black_box(from_slice::<Value>(black_box(CBOR)).unwrap()))
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
    bytes.iter()
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
    SingleFloat(f32),
    DoubleFloat(f64),
}

mod chumsky_zero_copy {
    use chumsky::prelude::*;
    use crate::i64_from_bytes;
    use super::CborZero;

    type Error<'a> = EmptyErr /*Rich<'a, u8>*/;

    fn int_out(slice: &[u8]) -> i64 {
        if slice.len() == 1 {
            (slice[0] & 0b1_1111) as i64
        } else {
            i64_from_bytes(&slice[1..])
        }
    }

    pub fn cbor<'a>() -> impl Parser<'a, &'a [u8], CborZero<'a>, extra::Err<Error<'a>>> {
        recursive(|data| {
            let read_int = any().then_with_ctx(
                any()
                    .repeated()
                    .try_configure(|cfg, ctx, _| {
                        let info = *ctx & 0b1_1111;
                        let num = if info < 24 {
                            0
                        } else if info < 28 {
                            2usize.pow(info as u32 - 24)
                        } else {
                            return Err(Error::empty() /*custom(span, format!("Invalid argument: {}", info))*/)
                        };
                        Ok(cfg.exactly(num))
                    })
            )
                .map_slice(int_out);

            let uint = read_int.map(CborZero::Int);
            let nint = read_int.map(|i| CborZero::Int(-1 - i));
            // TODO: Handle indefinite lengths
            let bstr = read_int
                .then_with_ctx(
                    any()
                        .repeated()
                        .configure(|cfg, ctx| {
                            cfg.exactly(*ctx as usize)
                        })
                        .map_slice(CborZero::Bytes)
                );

            let str = read_int
                .then_with_ctx(
                    any()
                        .repeated()
                        .configure(|cfg, ctx| {
                            cfg.exactly(*ctx as usize)
                        })
                        .map_slice(|slice| CborZero::String(std::str::from_utf8(slice).unwrap()))
                );

            let array = read_int
                .then_with_ctx(
                    data
                        .clone()
                        .with_ctx(())
                        .repeated()
                        .configure(|cfg, ctx| {
                            cfg.exactly(*ctx as usize)
                        })
                        .collect::<Vec<_>>()
                        .map(CborZero::Array)
                );

            let map = read_int
                .then_with_ctx(
                    data.clone()
                        .then(data.clone())
                        .with_ctx(())
                        .repeated()
                        .configure(|cfg, ctx| {
                            cfg.exactly(*ctx as usize)
                        })
                        .collect::<Vec<_>>()
                        .map(CborZero::Map)
                );

            let simple = |num: u8| any()
                .try_map(move |n, _| if n & 0b1_1111 == num {
                    Ok(())
                } else {
                    Err(Error::empty() /*custom(span, format!("Invalid simple identifier {}", n))*/)
                });

            let float_simple = choice((
                simple(20).to(CborZero::Bool(false)),
                simple(21).to(CborZero::Bool(true)),
                simple(22).to(CborZero::Null),
                simple(23).to(CborZero::Undef),
                simple(26).ignore_then(any()
                    .repeated_exactly::<4>()
                    .collect::<_, _, [_; 4]>()
                    .map(f32::from_be_bytes)
                    .map(CborZero::SingleFloat)
                ),
                simple(27).ignore_then(any()
                    .repeated_exactly::<8>()
                    .collect::<_, _, [_; 8]>()
                    .map(f64::from_be_bytes)
                    .map(CborZero::DoubleFloat)
                ),
            ));

            let major = |num: u8| any()
                .try_map(move |n, _| if (n >> 5) == num {
                    Ok(())
                } else {
                    Err(Error::empty() /*custom(span, format!("Invalid major version {}", n >> 5))*/)
                })
                .rewind();

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
