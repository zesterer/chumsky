use chumsky::prelude::*;
use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};

fn bench_choice(c: &mut Criterion) {
    let alphabet_choice = choice((
        just::<_, &str, extra::Default>('A'),
        just('B'),
        just('C'),
        just('D'),
        just('E'),
        just('F'),
        just('G'),
        just('H'),
        just('I'),
        just('J'),
        just('K'),
        just('L'),
        just('M'),
        just('N'),
        just('O'),
        just('P'),
        just('Q'),
        just('R'),
        just('S'),
        just('T'),
        just('U'),
        just('V'),
        just('W'),
        just('X'),
        just('Y'),
        just('Z'),
    ));

    let mut group = c.benchmark_group("choice");

    group.bench_function(BenchmarkId::new("choice::<(A..Z)>", "A"), |b| {
        b.iter(|| {
            black_box(Parser::parse(&alphabet_choice, black_box("A")))
                .into_result()
                .unwrap();
        })
    });

    group.bench_function(BenchmarkId::new("choice::<(A..Z)>", "Z"), |b| {
        b.iter(|| {
            black_box(alphabet_choice.parse(black_box("Z")))
                .into_result()
                .unwrap();
        })
    });

    group.bench_function(BenchmarkId::new("choice::<(A..Z)>", "0"), |b| {
        b.iter(|| {
            black_box(alphabet_choice.parse(black_box("0")))
                .into_result()
                .unwrap_err();
        })
    });
}

criterion_group!(benches, bench_choice);
criterion_main!(benches);
