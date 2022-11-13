use chumsky::zero_copy::prelude::*;

fn parser() -> impl for<'a> Parser<'a, str, char, Rich<str>> {
    just('a').or(just('b'))
}

fn main() {
    println!("{:?}", parser().parse("c"));
}
