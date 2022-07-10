use chumsky::{prelude::*, BoxStream, Flat, Stream};

type Span = std::ops::Range<usize>;

#[derive(Clone, Debug)]
enum Token {
    Int(u64),
    Ident(String),
    Op(String),
    OpenParen,
    CloseParen,
    BeginBlock,
    EndBlock,
}

#[derive(Debug)]
enum Delim {
    Paren,
    Block,
}

#[derive(Debug)]
enum TokenTree {
    Token(Token),
    Tree(Delim, Vec<(TokenTree, Span)>),
}

impl TokenTree {
    fn int(v: u64) -> Self {
        Self::Token(Token::Int(v))
    }

    fn ident(v: String) -> Self {
        Self::Token(Token::Ident(v))
    }

    fn op(v: String) -> Self {
        Self::Token(Token::Op(v))
    }

    fn open_paren() -> Self {
        Self::Token(Token::OpenParen)
    }

    fn close_paren() -> Self {
        Self::Token(Token::CloseParen)
    }

    fn begin_block() -> Self {
        Self::Token(Token::BeginBlock)
    }

    fn end_block() -> Self {
        Self::Token(Token::EndBlock)
    }

    fn paren_tree(tts: Vec<(TokenTree, Span)>) -> Self {
        Self::Tree(Delim::Paren, tts)
    }

    fn block_tree(tts: Vec<(TokenTree, Span)>) -> Self {
        Self::Tree(Delim::Block, tts)
    }
}

fn span_at(at: usize) -> Span {
    at..at + 1
}

fn span_of_tts(tts: &[(TokenTree, Span)]) -> Span {
    if tts.is_empty() {
        0..0
    } else {
        let start = tts.first().unwrap().1.start();
        let end = tts.last().unwrap().1.end();
        start..end
    }
}

// A parser that turns pythonic code with semantic whitespace into a token tree
fn lexer() -> impl Parser<char, Vec<(TokenTree, Span)>, Error = Simple<char>> {
    let int = text::int(10).from_str().unwrapped().map(TokenTree::int);

    let ident = text::ident().map(TokenTree::ident);

    let op = one_of("=.:%,")
        .repeated()
        .at_least(1)
        .collect()
        .map(TokenTree::op);

    let tt = recursive(|tt| {
        let tt_list = tt.padded().repeated();

        int.or(op)
            .or(ident)
            .or(tt_list
                .delimited_by(just('('), just(')'))
                .map(|tts| TokenTree::paren_tree(tts)))
            .map_with_span(|tt, span| (tt, span))
    });

    text::semantic_indentation(tt, |tts| {
        let span = span_of_tts(&tts);
        (TokenTree::block_tree(tts), span)
    })
    .then_ignore(end())
}

// Create a new flat token stream from a vector of nested tokens with
// the eoi (end of input) span
fn flatten_tts(eoi: Span, token_trees: Vec<(TokenTree, Span)>) -> BoxStream<'static, Token, Span> {
    use std::iter::once;

    Stream::from_nested(eoi, token_trees.into_iter(), |(tt, span)| match tt {
        TokenTree::Token(token) => Flat::Single((token, span)),
        TokenTree::Tree(Delim::Paren, tree) => Flat::Many(
            once((TokenTree::open_paren(), span_at(span.start)))
                .chain(tree.into_iter())
                .chain(once((
                    TokenTree::close_paren(),
                    span_at(span.end - 1), // One char before the `)`
                ))),
        ),
        TokenTree::Tree(Delim::Block, tree) => Flat::Many(
            once((TokenTree::begin_block(), span_at(span.start)))
                .chain(tree.into_iter())
                .chain(once((TokenTree::end_block(), span_at(span.end)))),
        ),
    })
}

fn main() {
    let src = include_str!("sample.py");
    let nested_tokens = lexer().parse(src);
    println!("Nested Tokens:\n{:#?}", nested_tokens);

    if let Ok(tts) = nested_tokens {
        // Chumsky currently only supports parsing linear streams of inputs
        // so convert nested tokens to flatten streams of tokens.
        let last_loc = span_of_tts(&tts).end();
        let eoi = last_loc..last_loc;
        let mut flatten_token_stream = flatten_tts(eoi, tts);

        // Show tokens.
        {
            let flatten_tokens = flatten_token_stream
                .fetch_tokens()
                .into_iter()
                .collect::<Vec<_>>();
            println!("Flatten Tokens:\n{:#?}", flatten_tokens);
        }

        // Parse the `flatten_token_stream` to build an AST.
        // See "nano_rust.rs" example
    }
}
