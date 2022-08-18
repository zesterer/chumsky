use chumsky::zero_copy::prelude::*;

fn parser() -> impl for<'a> Parser<'a, str, Rich<str>, Output = Vec<()>> {
    just('a').or(just('b'))
        .separated_by(just('!'))
        .ignored()
        .then(just("").ignored())
        .ignored()
        .repeated()
        .collect::<_>()
}

fn main() {
    let p = parser();
    p.find_problems();
    println!("{:?}", p.parse("c"));
}
