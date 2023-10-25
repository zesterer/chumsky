use chumsky::extra::ParserExtra;
use chumsky::input::IoInput;
use chumsky::prelude::*;
use std::env;
use std::fs::File;

#[allow(unused)]
#[derive(Debug)]
struct Foo {
    name: String,
    val: u32,
}

fn ident<'a, E: ParserExtra<'a, IoInput<File>>>() -> impl Parser<'a, IoInput<File>, String, E> {
    any()
        .filter(u8::is_ascii_alphabetic, "alphabetic")
        .repeated()
        .at_least(1)
        .collect::<Vec<_>>()
        .map(|v| String::from_utf8_lossy(&v).to_string())
}

fn digits<'a, E: ParserExtra<'a, IoInput<File>>>() -> impl Parser<'a, IoInput<File>, String, E> {
    any()
        .filter(u8::is_ascii_digit, "digit")
        .repeated()
        .at_least(1)
        .collect::<Vec<_>>()
        .map(|v| String::from_utf8_lossy(&v).to_string())
}

fn parser<'a, E: ParserExtra<'a, IoInput<File>>>() -> impl Parser<'a, IoInput<File>, Vec<Foo>, E> {
    group((ident(), just(b':').padded(), digits()))
        .map(|(name, _, digits)| Foo {
            name,
            val: digits.parse().unwrap(),
        })
        .separated_by(just(b'\n'))
        .allow_trailing()
        .collect()
}

fn main() {
    let src = File::open(env::args().nth(1).expect("Expected file argument"))
        .expect("Failed to open file");

    let json = parser::<extra::Err<Rich<_>>>()
        .parse(IoInput::new(src))
        .into_result();
    println!("{:#?}", json);
}
