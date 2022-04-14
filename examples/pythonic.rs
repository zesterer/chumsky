use chumsky::prelude::*;

#[derive(Debug)]
enum Delim {
    Paren,
    Block,
}

#[derive(Debug)]
enum Token {
    Int(u64),
    Ident(String),
    Op(String),
    Tree(Delim, Vec<Token>),
}

// A parser that turns pythonic code with semantic whitespace into a token tree
fn lexer() -> impl Parser<char, Vec<Token>, Error = Simple<char>> {
    let int = text::int(10).from_str().unwrapped().map(Token::Int);

    let ident = text::ident().map(Token::Ident);

    let op = one_of("=.:%,")
        .repeated()
        .at_least(1)
        .collect()
        .map(Token::Op);

    let tt = recursive(|tt| {
        let tt_list = tt.padded().repeated();

        int.or(op).or(ident).or(tt_list
            .delimited_by(just('('), just(')'))
            .map(|tts| Token::Tree(Delim::Paren, tts)))
    });

    text::semantic_indentation(tt, |tts| Token::Tree(Delim::Block, tts)).then_ignore(end())
}

fn main() {
    println!("{:#?}", lexer().parse(include_str!("sample.py")));
}
