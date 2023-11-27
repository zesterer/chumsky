use chumsky::prelude::*;

// This token is a tree: it contains within it a sub-tree of tokens
#[derive(PartialEq, Debug)]
enum Token {
    Num(i64),
    Add,
    Mul,
    Parens(Vec<Token>),
}

#[allow(clippy::let_and_return)]
fn parser<'a>() -> impl Parser<'a, &'a [Token], i64> {
    recursive(|expr| {
        let num = select_ref! { Token::Num(x) => *x };
        let parens = expr
            // Here we specify how the parser should come up with the nested tokens
            .nested_in(select_ref! { Token::Parens(xs) => xs.as_slice() });

        let atom = num.or(parens);

        let product = atom
            .clone()
            .foldl(just(&Token::Mul).ignore_then(atom).repeated(), |a, b| a * b);

        let sum = product
            .clone()
            .foldl(just(&Token::Add).ignore_then(product).repeated(), |a, b| {
                a + b
            });

        sum
    })
}

fn main() {
    // This token tree represents the expression `(2 + 3) * 4`
    let tokens = [
        Token::Parens(vec![Token::Num(2), Token::Add, Token::Num(3)]),
        Token::Mul,
        Token::Num(4),
    ];

    assert_eq!(parser().parse(&tokens).into_result(), Ok(20));
}
