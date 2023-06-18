use chumsky::prelude::*;
use chumsky_text::{input::StrInput, prelude::*};

fn parser<'a, C: Char, I: StrInput<'a, C>>() -> impl Parser<'a, I, Vec<&'a C::Str>> {
    regex("[a-zA-Z_][a-zA-Z0-9_]*")
        .padded()
        .repeated()
        .collect()
}

#[test]
fn regex_parser() {
    assert_eq!(
        parser().parse("hello world this works").into_result(),
        Ok(vec!["hello", "world", "this", "works"]),
    );

    assert_eq!(
        parser()
            .parse(b"hello world this works" as &[_])
            .into_result(),
        Ok(vec![
            b"hello" as &[_],
            b"world" as &[_],
            b"this" as &[_],
            b"works" as &[_],
        ]),
    );
}
