use chumsky::{input::MappedInput, prelude::*};

// This token is a tree: it contains within it a sub-tree of tokens
#[derive(PartialEq, Debug)]
enum Token {
    Num(i64),
    Add,
    Mul,
    Parens(Vec<(Token, SimpleSpan)>),
}

#[allow(clippy::let_and_return)]
fn parser<'src>(
) -> impl Parser<'src, MappedInput<'src, Token, SimpleSpan, &'src [(Token, SimpleSpan)]>, i64> {
    recursive(|expr| {
        let num = select_ref! { Token::Num(x) => *x };
        let parens = expr
            // Here we specify that `expr` should appear *inside* the parenthesised token tree
            .nested_in(select_ref! { Token::Parens(xs) = e => xs.split_token_span(e.span()) });

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
        (
            Token::Parens(vec![
                (Token::Num(2), SimpleSpan::new((), 1..2)),
                (Token::Add, SimpleSpan::new((), 3..4)),
                (Token::Num(3), SimpleSpan::new((), 5..6)),
            ]),
            SimpleSpan::new((), 0..7),
        ),
        (Token::Mul, SimpleSpan::new((), 8..9)),
        (Token::Num(4), SimpleSpan::new((), 10..11)),
    ];

    let eoi = SimpleSpan::new((), 11..11); // Example EoI

    assert_eq!(
        parser()
            .parse(tokens[..].split_token_span(eoi))
            .into_result(),
        Ok(20)
    );
}
