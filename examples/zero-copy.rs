use chumsky::prelude::*;

#[derive(PartialEq, Debug)]
enum Token<'a> {
    Ident(&'a str),
    String(&'a str),
}

// This parser is guaranteed to never allocate!
fn parser<'a>() -> impl Parser<'a, &'a str, [(SimpleSpan<usize>, Token<'a>); 6]> {
    let ident = any()
        .filter(|c: &char| c.is_alphanumeric())
        .repeated()
        .at_least(1)
        .to_slice()
        .map(Token::Ident);

    let string = just('"')
        .then(any().filter(|c: &char| *c != '"').repeated())
        .then(just('"'))
        .to_slice()
        .map(Token::String);

    ident
        .or(string)
        .map_with(|token, e| (e.span(), token))
        .padded()
        .repeated()
        .collect_exactly()
}

fn main() {
    assert_eq!(
        parser()
            .parse(r#"hello "world" these are "test" tokens"#)
            .into_result(),
        Ok([
            ((0..5).into(), Token::Ident("hello")),
            ((6..13).into(), Token::String("\"world\"")),
            ((14..19).into(), Token::Ident("these")),
            ((20..23).into(), Token::Ident("are")),
            ((24..30).into(), Token::String("\"test\"")),
            ((31..37).into(), Token::Ident("tokens")),
        ]),
    );
}
