use criterion::{black_box, criterion_group, criterion_main, Criterion};

#[derive(Debug, Clone, PartialEq)]
pub enum Json {
    Null,
    Bool(bool),
    Str(String),
    Num(f64),
    Array(Vec<Json>),
    Object(Vec<(String, Json)>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Token<'a> {
    Null,
    Bool(bool),
    Str(&'a [u8]),
    Num(f64),
    Ident(&'a [u8]),
    Less,
    More,
    LessEq,
    MoreEq,
    OpenParen,
    CloseParen,
    Comma,
}

static SAMPLE: &[u8] = include_bytes!("tokens.txt");

fn bench_lex(c: &mut Criterion) {
    c.bench_function("lex_chumsky_zero_copy", {
        use ::chumsky::prelude::*;
        let parser = chumsky_zero_copy::parser();
        move |b| {
            b.iter(|| {
                assert_eq!(
                    black_box(parser.parse(black_box(SAMPLE)))
                        .into_result()
                        .unwrap()
                        .len(),
                    4048
                )
            })
        }
    });

    c.bench_function("lex_chumsky_zero_copy_check", {
        use ::chumsky::prelude::*;
        let parser = chumsky_zero_copy::parser();
        move |b| {
            b.iter(|| {
                assert!(black_box(parser.check(black_box(SAMPLE)))
                    .into_errors()
                    .is_empty())
            })
        }
    });

    c.bench_function("lex_logos", |b| {
        b.iter(|| {
            assert!(black_box(logos::lexer(black_box(SAMPLE))).all(|t| t != Ok(logos::Token::Error)))
        })
    });
}

criterion_group!(benches, bench_lex);
criterion_main!(benches);

mod logos {
    use logos::{Lexer, Logos};
    use std::str;

    fn to_bool<'a>(lex: &mut Lexer<'a, Token<'a>>) -> bool {
        match lex.slice() {
            b"true" => true,
            b"false" => false,
            _ => unreachable!(),
        }
    }

    fn to_f64<'a>(lex: &mut Lexer<'a, Token<'a>>) -> f64 {
        str::from_utf8(lex.slice()).unwrap().parse().unwrap()
    }

    #[derive(Logos, Debug, Clone, PartialEq)]
    pub enum Token<'a> {
        #[token("null")]
        Null,
        #[regex("true|false", to_bool)]
        Bool(bool),
        #[regex(br#""([^\\"]|\\[\\"bfnrt/])*""#)]
        Str(&'a [u8]),
        #[regex(br"-?([1-9][0-9]*|0)(\.[0-9]*)?([eE][+-]?[0-9]*)?", to_f64)]
        Num(f64),
        #[regex(br"[a-zA-Z_][a-zA-Z0-9_]*")]
        Ident(&'a [u8]),
        #[token(b"<")]
        Less,
        #[token(b">")]
        More,
        #[token(b"<=")]
        LessEq,
        #[token(b">=")]
        MoreEq,
        #[token(b"(")]
        OpenParen,
        #[token(b")")]
        CloseParen,
        #[token(b",")]
        Comma,

        #[regex(br"\s", logos::skip)]
        Error,
    }

    pub fn lexer(src: &[u8]) -> Lexer<'_, Token<'_>> {
        Token::lexer(src)
    }
}

mod chumsky_zero_copy {
    use chumsky::prelude::*;

    use super::Token;
    use std::str;

    pub fn parser<'a>() -> impl Parser<'a, &'a [u8], Vec<Token<'a>>> {
        let digits = one_of(b'0'..=b'9').repeated().to_slice();

        let int = one_of(b'1'..=b'9')
            .repeated()
            .at_least(1)
            .then(one_of(b'0'..=b'9').repeated())
            .ignored()
            .or(just(b'0').ignored())
            .ignored();

        let frac = just(b'.').then(digits.clone());

        let exp = just(b'e')
            .or(just(b'E'))
            .then(one_of(b"+-").or_not())
            .then(digits.clone());

        let number = just(b'-')
            .or_not()
            .then(int)
            .then(frac.or_not())
            .then(exp.or_not())
            .to_slice()
            .map(|bytes| str::from_utf8(bytes).unwrap().parse().unwrap())
            .boxed();

        let escape = just(b'\\')
            .then(choice((
                just(b'\\'),
                just(b'/'),
                just(b'"'),
                just(b'b').to(b'\x08'),
                just(b'f').to(b'\x0C'),
                just(b'n').to(b'\n'),
                just(b'r').to(b'\r'),
                just(b't').to(b'\t'),
            )))
            .ignored()
            .boxed();

        let string = none_of(b"\\\"")
            .ignored()
            .or(escape)
            .repeated()
            .to_slice()
            .delimited_by(just(b'"'), just(b'"'))
            .boxed();

        let ident = text::ascii::ident().to_slice().map(Token::Ident);

        choice((
            just(b"null").to(Token::Null),
            just(b"true").to(Token::Bool(true)),
            just(b"false").to(Token::Bool(false)),
            number.map(Token::Num),
            string.map(Token::Str),
            ident,
            just(b"<=").to(Token::LessEq),
            just(b">=").to(Token::MoreEq),
            just(b"<").to(Token::Less),
            just(b">").to(Token::More),
            just(b"(").to(Token::OpenParen),
            just(b")").to(Token::CloseParen),
            just(b",").to(Token::Comma),
        ))
        .padded()
        .repeated()
        .collect()
    }
}
