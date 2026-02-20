use chumsky::{pratt::*, prelude::*};
use criterion::{criterion_group, criterion_main, Criterion};
use std::hint::black_box;

mod utils;

static CORPUS: &str = include_str!("samples/pratt.txt");

fn bench_pratt(c: &mut Criterion) {
    c.bench_function("pratt", {
        move |b| b.iter(|| black_box(parser().parse(CORPUS)).unwrap())
    });
}

criterion_group!(
    name = benches;
    config = utils::make_criterion();
    targets = bench_pratt
);

criterion_main!(benches);

pub enum Expr {
    Num(i64),
    Neg(Box<Self>),
    Fact(Box<Self>),
    Pow(Box<Self>, Box<Self>),
    Mul(Box<Self>, Box<Self>),
    Div(Box<Self>, Box<Self>),
    Rem(Box<Self>, Box<Self>),
    Add(Box<Self>, Box<Self>),
    Sub(Box<Self>, Box<Self>),
}

fn parser<'src>() -> impl Parser<'src, &'src str, Expr> {
    recursive(|expr| {
        let num = text::int(10).map(|s: &str| Expr::Num(s.parse().unwrap()));

        let atom = choice((num, expr.delimited_by(just('('), just(')')))).padded();

        let op = |c| just(c).padded();

        atom.pratt((
            postfix(10, op('!'), |x, _, _| Expr::Fact(Box::new(x))),
            prefix(5, op('-'), |_, x, _| Expr::Neg(Box::new(x))),
            infix(right(10), op('^'), |x, _, y, _| {
                Expr::Pow(Box::new(x), Box::new(y))
            }),
            infix(left(8), op('*'), |x, _, y, _| {
                Expr::Mul(Box::new(x), Box::new(y))
            }),
            infix(left(8), op('/'), |x, _, y, _| {
                Expr::Div(Box::new(x), Box::new(y))
            }),
            infix(left(8), op('%'), |x, _, y, _| {
                Expr::Rem(Box::new(x), Box::new(y))
            }),
            infix(left(2), op('+'), |x, _, y, _| {
                Expr::Add(Box::new(x), Box::new(y))
            }),
            infix(left(2), op('-'), |x, _, y, _| {
                Expr::Sub(Box::new(x), Box::new(y))
            }),
        ))
    })
}
