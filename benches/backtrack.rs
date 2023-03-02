use chumsky::prelude::*;
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn bench_backtrack(c: &mut Criterion) {
    let four = just::<_, &str, extra::Default>('!')
        .repeated()
        .collect::<Vec<_>>()
        .then_ignore(just(';'))
        .repeated()
        .exactly(4)
        .collect::<Vec<_>>()
        .then_ignore(just(';'));

    let five = just('!')
        .repeated()
        .collect::<Vec<_>>()
        .then_ignore(just(';'))
        .repeated()
        .exactly(5)
        .collect::<Vec<_>>()
        .then_ignore(just(';'));

    let xs = five.or(four).repeated().collect::<Vec<_>>();

    c.bench_function("backtrack", |b| {
        b.iter(|| {
            black_box(xs.parse(&black_box("!!!!;!!!!;!!!!;!!!!;;".repeat(1000))))
                .into_result()
                .unwrap();
        })
    });
}

criterion_group!(benches, bench_backtrack);
criterion_main!(benches);
