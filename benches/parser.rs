use chumsky::prelude::*;
use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};

mod utils;

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

pub fn bench_or(c: &mut Criterion) {
    let mut group = c.benchmark_group("or");

    let many_or = just::<_, _, extra::Default>('A')
        .or(just('B'))
        .or(just('C'))
        .or(just('D'))
        .or(just('E'))
        .or(just('F'))
        .or(just('G'))
        .or(just('H'))
        .or(just('I'))
        .or(just('J'))
        .or(just('K'))
        .or(just('L'))
        .or(just('M'));

    group.bench_function(BenchmarkId::new("A.or(B)...or(M)", "A"), |b| {
        b.iter(|| {
            black_box(many_or.parse(black_box("A")))
                .into_result()
                .unwrap();
        })
    });

    group.bench_function(BenchmarkId::new("A.or(B)...or(M)", "M"), |b| {
        b.iter(|| {
            black_box(many_or.parse(black_box("M")))
                .into_result()
                .unwrap();
        })
    });

    group.bench_function(BenchmarkId::new("A.or(B)...or(M)", "0"), |b| {
        b.iter(|| {
            black_box(many_or.parse(black_box("0")))
                .into_result()
                .unwrap_err();
        })
    });
}

criterion_group!(
    name = benches;
    config = utils::make_criterion();
    targets = bench_choice, bench_or,
);
criterion_main!(benches);
