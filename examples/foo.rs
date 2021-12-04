/// This is the parser and interpreter for the 'Foo' language. See `tutorial.md` in the repository's root to learn
/// about it.
use chumsky::prelude::*;

#[derive(Debug)]
enum Expr {
    Num(f64),

    Neg(Box<Expr>),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),

    Let {
        name: String,
        rhs: Box<Expr>,
        then: Box<Expr>,
    },
    Fn {
        name: String,
        args: Vec<String>,
        rhs: Box<Expr>,
        then: Box<Expr>,
    },
}

fn parser() -> impl Parser<char, Expr, Error = Simple<char>> {
    recursive(|expr| {
        let int = text::int(10)
            .map(|s: String| Expr::Num(s.parse().unwrap()))
            .padded();

        let atom = int.or(expr.delimited_by('(', ')'));

        let op = |c| just(c).padded();

        let unary = op('-')
            .repeated()
            .then(atom)
            .foldr(|_op, rhs| Expr::Neg(Box::new(rhs)));

        let product = unary
            .clone()
            .then(
                op('*')
                    .to(Expr::Mul as fn(_, _) -> _)
                    .or(op('/').to(Expr::Div as fn(_, _) -> _))
                    .then(unary)
                    .repeated(),
            )
            .foldl(|lhs, (op, rhs)| op(Box::new(lhs), Box::new(rhs)));

        let sum = product
            .clone()
            .then(
                op('+')
                    .to(Expr::Add as fn(_, _) -> _)
                    .or(op('-').to(Expr::Sub as fn(_, _) -> _))
                    .then(product)
                    .repeated(),
            )
            .foldl(|lhs, (op, rhs)| op(Box::new(lhs), Box::new(rhs)));

        sum
    })
    .padded()
    .then_ignore(end())
}

fn eval(expr: Expr) -> Result<f64, String> {
    match expr {
        Expr::Num(x) => Ok(x),
        Expr::Neg(a) => Ok(-eval(*a)?),
        Expr::Add(a, b) => Ok(eval(*a)? + eval(*b)?),
        Expr::Sub(a, b) => Ok(eval(*a)? - eval(*b)?),
        Expr::Mul(a, b) => Ok(eval(*a)? * eval(*b)?),
        Expr::Div(a, b) => Ok(eval(*a)? / eval(*b)?),
        _ => todo!(),
    }
}

fn main() {
    let src = std::fs::read_to_string(std::env::args().nth(1).unwrap()).unwrap();

    match parser().parse(src) {
        Ok(ast) => match eval(ast) {
            Ok(output) => println!("{}", output),
            Err(eval_err) => println!("Evaluation error: {}", eval_err),
        },
        Err(parse_errs) => parse_errs
            .into_iter()
            .for_each(|e| println!("Parse error: {}", e)),
    }
}
