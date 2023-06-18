#[cfg(feature = "memoization")]
use chumsky::prelude::*;

#[test]
#[cfg(feature = "memoization")]
fn exponential() {
    fn parser<'a>() -> impl Parser<'a, &'a str, String> {
        recursive(|expr| {
            let atom = any()
                .filter(|c: &char| c.is_alphabetic())
                .repeated()
                .at_least(1)
                .collect()
                .or(expr.delimited_by(just('('), just(')')));

            atom.clone()
                .then_ignore(just('+'))
                .then(atom.clone())
                .map(|(a, b)| format!("{}{}", a, b))
                .memoised()
                .or(atom)
        })
        .then_ignore(end())
    }

    parser()
        .parse("((((((((((((((((((((((((((((((a+b))))))))))))))))))))))))))))))")
        .into_result()
        .unwrap();
}

#[test]
#[cfg(feature = "memoization")]
fn left_recursive() {
    fn parser<'a>() -> impl Parser<'a, &'a str, String> {
        recursive(|expr| {
            let atom = any()
                .filter(|c: &char| c.is_alphabetic())
                .repeated()
                .at_least(1)
                .collect();

            let sum = expr
                .clone()
                .then_ignore(just('+'))
                .then(expr)
                .map(|(a, b)| format!("{}{}", a, b))
                .memoised();

            sum.or(atom)
        })
        .then_ignore(end())
    }

    assert_eq!(parser().parse("a+b+c").into_result().unwrap(), "abc");
}
