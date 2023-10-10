use chumsky::{input::SpannedInput, prelude::*};

// This token is a tree: it contains within it a sub-tree of tokens
#[derive(PartialEq, Debug)]
enum Token {
    Num(i64),
    Add,
    Mul,
    Parens(Vec<(Token, SimpleSpan)>),
}

type TokenTreeInput<'a> = SpannedInput<Token, SimpleSpan, &'a [(Token, SimpleSpan)]>;

fn parser<'a>() -> impl Parser<'a, TokenTreeInput<'a>, i64> {
    recursive(|expr| {
        let num = select_ref! { Token::Num(x) => *x };
        let parens = expr
            // Here we specify how the parser should come up with the nested tokens
            .nested_in(select_ref! {
                Token::Parens(xs) = e => xs.as_slice().spanned(SimpleSpan::to_end(&e.span())),
            });

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
                (Token::Num(2), SimpleSpan::new(1, 2)),
                (Token::Add, SimpleSpan::new(3, 4)),
                (Token::Num(3), SimpleSpan::new(5, 6)),
            ]),
            SimpleSpan::new(0, 7),
        ),
        (Token::Mul, SimpleSpan::new(8, 9)),
        (Token::Num(4), SimpleSpan::new(10, 11)),
    ];

    let eoi = SimpleSpan::new(11, 11); // Example EoI

    assert_eq!(
        parser().parse(tokens[..].spanned(eoi)).into_result(),
        Ok(20)
    );
}
