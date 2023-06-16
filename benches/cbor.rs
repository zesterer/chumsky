use criterion::{criterion_group, criterion_main, Criterion};
use std::hint::black_box;

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
                .map_slice(int_out);

            let uint = read_int.map(CborZero::Int);
            let nint = read_int.map(|i| CborZero::Int(-1 - i));
            // TODO: Handle indefinite lengths
            let bstr = read_int.ignore_with_ctx(
                any()
                    .repeated()
                    .configure(|cfg, ctx| cfg.exactly(*ctx as usize))
                    .map_slice(CborZero::Bytes),
            );

            let str = read_int.ignore_with_ctx(
                any()
                    .repeated()
                    .configure(|cfg, ctx| cfg.exactly(*ctx as usize))
                    .map_slice(|slice| CborZero::String(std::str::from_utf8(slice).unwrap())),
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
