use chumsky::{prelude::*, BoxStream, Flat};
use std::ops::Range;

// Represents the different kinds of delimiters we care about
#[derive(Copy, Clone, Debug)]
enum Delim {
    Paren,
    Block,
}

// An 'atomic' token (i.e: it has no child tokens)
#[derive(Clone, Debug)]
enum Token {
    Int(u64),
    Ident(String),
    Op(String),
    Open(Delim),
    Close(Delim),
}

// The output of the lexer: a recursive tree of nested tokens
#[derive(Debug)]
enum TokenTree {
    Token(Token),
    Tree(Delim, Vec<Spanned<TokenTree>>),
}

type Span = Range<usize>;

type Spanned<T> = (T, Span);

// A parser that turns pythonic code with semantic whitespace into a token tree
fn lexer() -> impl Parser<char, Vec<Spanned<TokenTree>>, Error = Simple<char>> {
    let tt = recursive(|tt| {
        // Define some atomic tokens
        let int = text::int(10).from_str().unwrapped().map(Token::Int);
        let ident = text::ident().map(Token::Ident);
        let op = one_of("=.:%,")
            .repeated()
            .at_least(1)
            .collect()
            .map(Token::Op);

        let single_token = int.or(op).or(ident).map(TokenTree::Token);

        // Tokens surrounded by parentheses get turned into parenthesised token trees
        let token_tree = tt
            .padded()
            .repeated()
            .delimited_by(just('('), just(')'))
            .map(|tts| TokenTree::Tree(Delim::Paren, tts));

        single_token
            .or(token_tree)
            .map_with_span(|tt, span| (tt, span))
    });

    // Whitespace indentation creates code block token trees
    text::semantic_indentation(tt, |tts, span| (TokenTree::Tree(Delim::Block, tts), span))
        .then_ignore(end())
}

/// Flatten a series of token trees into a single token stream, ready for feeding into the main parser
fn tts_to_stream(
    eoi: Span,
    token_trees: Vec<Spanned<TokenTree>>,
) -> BoxStream<'static, Token, Span> {
    use std::iter::once;

    BoxStream::from_nested(eoi, token_trees.into_iter(), |(tt, span)| match tt {
        // Single tokens remain unchanged
        TokenTree::Token(token) => Flat::Single((token, span)),
        // Nested token trees get flattened into their inner contents, surrounded by `Open` and `Close` tokens
        TokenTree::Tree(delim, tree) => Flat::Many(
            once((TokenTree::Token(Token::Open(delim)), span.clone()))
                .chain(tree.into_iter())
                .chain(once((TokenTree::Token(Token::Close(delim)), span))),
        ),
    })
}

fn main() {
    let code = include_str!("sample.py");

    // First, lex the code into some nested token trees
    let tts = lexer().parse(code).unwrap();

    println!("--- Token Trees ---\n{:#?}", tts);

    // Next, flatten
    let eoi = 0..code.chars().count();
    let mut token_stream = tts_to_stream(eoi, tts);

    // At this point, we have a token stream that can be fed into the main parser! Because this is just an example,
    // we're instead going to just collect the token stream into a vector and print it.

    let flattened_trees = token_stream.fetch_tokens().collect::<Vec<_>>();

    println!("--- Flattened Token Trees ---\n{:?}", flattened_trees);
}
