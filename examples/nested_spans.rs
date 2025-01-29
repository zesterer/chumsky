use chumsky::{input::BorrowInput, prelude::*};

// This token is a tree: it contains within it a sub-tree of tokens
#[derive(PartialEq, Debug)]
enum Token {
    Num(i64),
    Add,
    Mul,
    Parens(Vec<(Token, SimpleSpan)>),
}

#[allow(clippy::let_and_return)]
fn parser<'src, I, M>(make_input: M) -> impl Parser<'src, I, i64>
where
    I: BorrowInput<'src, Token = Token, Span = SimpleSpan>,
    M: Fn(SimpleSpan, &'src [(Token, SimpleSpan)]) -> I + Clone + 'src,
{
    recursive(|expr| {
        let num = select_ref! { Token::Num(x) => *x };
        let parens = expr
            // Here we specify that `expr` should appear *inside* the parenthesised token tree
            .nested_in(select_ref! { Token::Parens(xs) = e => make_input(e.span(), xs) });

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

fn make_input(
    eoi: SimpleSpan,
    toks: &[(Token, SimpleSpan)],
) -> impl BorrowInput<'_, Token = Token, Span = SimpleSpan> {
    toks.map(eoi, |(t, s)| (t, s))
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
        parser(make_input)
            .parse(make_input(eoi, &tokens))
            .into_result(),
        Ok(20)
    );
}
