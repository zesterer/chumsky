//! This is a Brainfuck parser and interpreter
//! Run it with the following command:
//! cargo run --example debug

use chumsky::prelude::*;
use std::{
    collections::HashMap,
    env, fs,
    io::{self, Read},
};

#[derive(Clone)]
enum Instr {
    Invalid,
    Left,
    Right,
    Incr,
    Decr,
    Read,
    Write,
    Loop(Vec<Self>),
}

fn bf<'a>() -> impl Parser<'a, &'a str, Vec<Instr>, extra::Err<Simple<'a, char>>> {
    use Instr::*;
    recursive(|bf| {
        choice((
            just('<').to(Left),
            just('>').to(Right),
            just('+').to(Incr),
            just('-').to(Decr),
            just(',').to(Read),
            just('.').to(Write),
            bf.delimited_by(just('['), just(']')).map(Loop),
        ))
        .repeated()
        .collect()
    })
}

#[derive(Clone, Debug)]
pub enum Json {
    Null,
    Bool(bool),
    Str(String),
    Num(f64),
    Array(Vec<Json>),
    Object(HashMap<String, Json>),
}

fn json<'a>() -> impl Parser<'a, &'a str, Json> {
    recursive(|value| {
        let digits = text::digits(10).to_slice();

        let frac = just('.').then(digits);

        let exp = just('e')
            .or(just('E'))
            .then(one_of("+-").or_not())
            .then(digits);

        let number = just('-')
            .or_not()
            .then(text::int(10))
            .then(frac.or_not())
            .then(exp.or_not())
            .to_slice()
            .map(|s: &str| s.parse().unwrap());

        let escape = just('\\')
            .then(choice((
                just('\\'),
                just('/'),
                just('"'),
                just('b').to('\x08'),
                just('f').to('\x0C'),
                just('n').to('\n'),
                just('r').to('\r'),
                just('t').to('\t'),
                just('u').ignore_then(text::digits(16).exactly(4).to_slice().validate(
                    |digits, _, emitter| {
                        char::from_u32(u32::from_str_radix(digits, 16).unwrap()).unwrap_or_else(
                            || {
                                emitter.emit(Default::default());
                                '\u{FFFD}' // unicode replacement character
                            },
                        )
                    },
                )),
            )))
            .ignored();

        let string = none_of("\\\"")
            .ignored()
            .or(escape)
            .repeated()
            .to_slice()
            .map(ToString::to_string)
            .delimited_by(just('"'), just('"'));

        let array = value
            .clone()
            .separated_by(just(',').padded())
            .allow_trailing()
            .collect()
            .padded()
            .delimited_by(just('['), just(']'));

        let member = string.then_ignore(just(':').padded()).then(value);
        let object = member
            .clone()
            .separated_by(just(',').padded())
            .collect()
            .padded()
            .delimited_by(just('{'), just('}'));

        choice((
            just("null").to(Json::Null),
            just("true").to(Json::Bool(true)),
            just("false").to(Json::Bool(false)),
            number.map(Json::Num).labelled("number"),
            string.map(Json::Str).labelled("string"),
            array.map(Json::Array).labelled("array"),
            object.map(Json::Object).labelled("object"),
        ))
        .padded()
        .labelled("JSON value")
    })
}

fn main() {
    let node_info = json().node_info(&mut Default::default());
    // println!("{}", node_info.to_graph().to_dot_string().unwrap());
    // println!("{}", node_info.to_ebnf());
    println!("{}", node_info.to_railroad_svg());
}
