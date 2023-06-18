use chumsky::{input::WithContext, prelude::*};
use chumsky_text::prelude::*;

#[test]
fn zero_copy() {
    #[derive(PartialEq, Debug)]
    enum Token<'a> {
        Ident(&'a str),
        String(&'a str),
    }

    type FileId = u32;

    type Span = (FileId, SimpleSpan<usize>);

    fn parser<'a>() -> impl Parser<'a, WithContext<FileId, &'a str>, [(Span, Token<'a>); 6]> {
        let ident = any()
            .filter(|c: &char| c.is_alphanumeric())
            .repeated()
            .at_least(1)
            .map_slice(Token::Ident);

        let string = just('"')
            .then(any().filter(|c: &char| *c != '"').repeated())
            .then(just('"'))
            .map_slice(Token::String);

        ident
            .or(string)
            .map_with_span(|token, span| (span, token))
            .padded()
            .repeated()
            .collect_exactly()
    }

    assert_eq!(
        parser()
            .parse(r#"hello "world" these are "test" tokens"#.with_context(42))
            .into_result(),
        Ok([
            ((42, (0..5).into()), Token::Ident("hello")),
            ((42, (6..13).into()), Token::String("\"world\"")),
            ((42, (14..19).into()), Token::Ident("these")),
            ((42, (20..23).into()), Token::Ident("are")),
            ((42, (24..30).into()), Token::String("\"test\"")),
            ((42, (31..37).into()), Token::Ident("tokens")),
        ]),
    );
}

#[test]
fn zero_copy_repetition() {
    fn parser<'a>() -> impl Parser<'a, &'a str, Vec<u64>> {
        any()
            .filter(|c: &char| c.is_ascii_digit())
            .repeated()
            .at_least(1)
            .at_most(3)
            .map_slice(|b: &str| b.parse::<u64>().unwrap())
            .padded()
            .separated_by(just(',').padded())
            .allow_trailing()
            .collect()
            .delimited_by(just('['), just(']'))
    }

    assert_eq!(
        parser().parse("[122 , 23,43,    4, ]").into_result(),
        Ok(vec![122, 23, 43, 4]),
    );
    assert_eq!(
        parser().parse("[0, 3, 6, 900,120]").into_result(),
        Ok(vec![0, 3, 6, 900, 120]),
    );
    assert_eq!(
        parser().parse("[200,400,50  ,0,0, ]").into_result(),
        Ok(vec![200, 400, 50, 0, 0]),
    );

    assert!(parser().parse("[1234,123,12,1]").has_errors());
    assert!(parser().parse("[,0, 1, 456]").has_errors());
    assert!(parser().parse("[3, 4, 5, 67 89,]").has_errors());
}

#[test]
fn zero_copy_group() {
    fn parser<'a>() -> impl Parser<'a, &'a str, (&'a str, u64, char)> {
        group((
            any()
                .filter(|c: &char| c.is_ascii_alphabetic())
                .repeated()
                .at_least(1)
                .slice()
                .padded(),
            any()
                .filter(|c: &char| c.is_ascii_digit())
                .repeated()
                .at_least(1)
                .map_slice(|s: &str| s.parse::<u64>().unwrap())
                .padded(),
            any().filter(|c: &char| !c.is_whitespace()).padded(),
        ))
    }

    assert_eq!(
        parser().parse("abc 123 [").into_result(),
        Ok(("abc", 123, '[')),
    );
    assert_eq!(
        parser().parse("among3d").into_result(),
        Ok(("among", 3, 'd')),
    );
    assert_eq!(
        parser().parse("cba321,").into_result(),
        Ok(("cba", 321, ',')),
    );

    assert!(parser().parse("abc 123  ").has_errors());
    assert!(parser().parse("123abc ]").has_errors());
    assert!(parser().parse("and one &").has_errors());
}

#[test]
fn zero_copy_group_array() {
    fn parser<'a>() -> impl Parser<'a, &'a str, [char; 3]> {
        group([just('a'), just('b'), just('c')])
    }

    assert_eq!(parser().parse("abc").into_result(), Ok(['a', 'b', 'c']));
    assert!(parser().parse("abd").has_errors());
}
