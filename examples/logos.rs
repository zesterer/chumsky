//! An example of using logos with chumsky to parse sexprs
//! Run it with the following command:
//! cargo run --example logos

use ariadne::{Color, Label, Report, ReportKind, Source};
use chumsky::{
    input::{Stream, ValueInput},
    prelude::*,
};
use logos::Logos;
use std::fmt;

#[derive(Logos, Clone, PartialEq)]
enum Token<'a> {
    Error,

    #[regex(r"[+-]?([0-9]*[.])?[0-9]+")]
    Float(&'a str),

    #[token("+")]
    Add,
    #[token("-")]
    Sub,
    #[token("*")]
    Mul,
    #[token("/")]
    Div,

    #[token("(")]
    LParen,
    #[token(")")]
    RParen,

    #[regex(r"[ \t\f\n]+", logos::skip)]
    Whitespace,
}

impl fmt::Display for Token<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Float(s) => write!(f, "{s}"),
            Self::Add => write!(f, "+"),
            Self::Sub => write!(f, "-"),
            Self::Mul => write!(f, "*"),
            Self::Div => write!(f, "/"),
            Self::LParen => write!(f, "("),
            Self::RParen => write!(f, ")"),
            Self::Whitespace => write!(f, "<whitespace>"),
            Self::Error => write!(f, "<error>"),
        }
    }
}

#[derive(Debug)]
enum SExpr {
    Float(f64),
    Add,
    Sub,
    Mul,
    Div,
    List(Vec<Self>),
}

// This function signature looks complicated, but don't fear! We're just saying that this function is generic over
// inputs that:
//     - Can have tokens pulled out of them by-value, by cloning (`ValueInput`)
//     - Gives us access to slices of the original input (`SliceInput`)
//     - Produces tokens of type `Token`, the type we defined above (`Token = Token<'a>`)
//     - Produces spans of type `SimpleSpan`, a built-in span type provided by chumsky (`Span = SimpleSpan`)
// The function then returns a parser that:
//     - Has an input type of type `I`, the one we declared as a type parameter
//     - Produces an `SExpr` as its output
//     - Uses `Rich`, a built-in error type provided by chumsky, for error generation
fn parser<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, SExpr, extra::Err<Rich<'tokens, Token<'src>>>>
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = SimpleSpan>,
{
    recursive(|sexpr| {
        let atom = select! {
            Token::Float(x) => SExpr::Float(x.parse().unwrap()),
            Token::Add => SExpr::Add,
            Token::Sub => SExpr::Sub,
            Token::Mul => SExpr::Mul,
            Token::Div => SExpr::Div,
        };

        let list = sexpr
            .repeated()
            .collect()
            .map(SExpr::List)
            .delimited_by(just(Token::LParen), just(Token::RParen));

        atom.or(list)
    })
}

impl SExpr {
    // Recursively evaluate an s-expression
    fn eval(&self) -> Result<f64, &'static str> {
        match self {
            Self::Float(x) => Ok(*x),
            Self::Add => Err("Cannot evaluate operator '+'"),
            Self::Sub => Err("Cannot evaluate operator '-'"),
            Self::Mul => Err("Cannot evaluate operator '*'"),
            Self::Div => Err("Cannot evaluate operator '/'"),
            Self::List(list) => match &list[..] {
                [Self::Add, tail @ ..] => tail.iter().map(SExpr::eval).sum(),
                [Self::Mul, tail @ ..] => tail.iter().map(SExpr::eval).product(),
                [Self::Sub, init, tail @ ..] => {
                    Ok(init.eval()? - tail.iter().map(SExpr::eval).sum::<Result<f64, _>>()?)
                }
                [Self::Div, init, tail @ ..] => {
                    Ok(init.eval()? / tail.iter().map(SExpr::eval).product::<Result<f64, _>>()?)
                }
                _ => Err("Cannot evaluate list"),
            },
        }
    }
}

const SRC: &str = r"
    (-
        (* (+ 4 7.3) 7)
        (/ 5 3)
    )
";

fn main() {
    // Create a logos lexer over the source code
    let token_iter = Token::lexer(SRC)
        .spanned()
        // Convert logos errors into tokens. We want parsing to be recoverable and not fail at the lexing stage, so
        // we have a dedicated `Token::Error` variant that represents a token error that was previously encountered
        .map(|(tok, span)| match tok {
            // Turn the `Range<usize>` spans logos gives us into chumsky's `SimpleSpan` via `Into`, because it's easier
            // to work with
            Ok(tok) => (tok, span.into()),
            Err(()) => (Token::Error, span.into()),
        });

    // Turn the token iterator into a stream that chumsky can use for things like backtracking
    let token_stream = Stream::from_iter(token_iter)
        // Tell chumsky to split the (Token, SimpleSpan) stream into its parts so that it can handle the spans for us
        // This involves giving chumsky an 'end of input' span: we just use a zero-width span at the end of the string
        .map((0..SRC.len()).into(), |(t, s): (_, _)| (t, s));

    // Parse the token stream with our chumsky parser
    match parser().parse(token_stream).into_result() {
        // If parsing was successful, attempt to evaluate the s-expression
        Ok(sexpr) => match sexpr.eval() {
            Ok(out) => println!("Result = {out}"),
            Err(err) => println!("Runtime error: {err}"),
        },
        // If parsing was unsuccessful, generate a nice user-friendly diagnostic with ariadne. You could also use
        // codespan, or whatever other diagnostic library you care about. You could even just display-print the errors
        // with Rust's built-in `Display` trait, but it's a little crude
        Err(errs) => {
            for err in errs {
                Report::build(ReportKind::Error, ((), err.span().into_range()))
                    .with_config(ariadne::Config::new().with_index_type(ariadne::IndexType::Byte))
                    .with_code(3)
                    .with_message(err.to_string())
                    .with_label(
                        Label::new(((), err.span().into_range()))
                            .with_message(err.reason().to_string())
                            .with_color(Color::Red),
                    )
                    .finish()
                    .eprint(Source::from(SRC))
                    .unwrap();
            }
        }
    }
}
