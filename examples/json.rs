use chumsky::prelude::*;
use std::{collections::HashMap, env, fs};

#[derive(Clone, Debug)]
enum Json {
    Null,
    Bool(bool),
    Str(String),
    Num(f64),
    Array(Vec<Json>),
    Object(HashMap<String, Json>)
}

fn parser() -> impl Parser<char, Json, Error = Simple<char>> {
    recursive(|value| {
        let frac = just('.').chain(text::digits());

        let exp = just('e').or(just('E'))
            .padding_for(just('+').or(just('-')).or_not())
            .chain(text::digits());

        let number = just('-').or_not()
            .chain(text::int())
            .chain(frac.or_not().flatten())
            .chain::<char, _, _>(exp.or_not().flatten())
            .collect::<String>()
            .map(|s| s.parse().unwrap());

        let escape = just('\\')
            .padding_for(just('\\')
            .or(just('/'))
            .or(just('"'))
            .or(just('b').to('\x08'))
            .or(just('f').to('\x0C'))
            .or(just('n').to('\n'))
            .or(just('r').to('\r'))
            .or(just('t').to('\t')));

        let string = just('"')
            .padding_for(filter(|c| *c != '\\' && *c != '"').or(escape).repeated())
            .padded_by(just('"'))
            .collect::<String>();

        let array = value.clone()
            .chain(just(',').padding_for(value.clone()).repeated())
            .or_not()
            .flatten()
            .delimited_by('[', ']')
            .map(|x| x.unwrap_or_else(Vec::new));

        let member = string.padded_by(just(':').padded()).then(value);
        let object = member.clone()
            .chain(just(',').padded().padding_for(member).repeated())
            .or_not()
            .flatten()
            .padded()
            .delimited_by('{', '}')
            .map(|x| x.unwrap_or_else(Vec::new))
            .collect::<HashMap<String, Json>>();

        seq("null".chars()).to(Json::Null)
            .or(seq("true".chars()).to(Json::Bool(true)))
            .or(seq("false".chars()).to(Json::Bool(false)))
            .or(number.map(Json::Num))
            .or(string.map(Json::Str))
            .or(array.map(Json::Array))
            .or(object.map(Json::Object))
            .padded()
    })
}

fn main() {
    let src = fs::read_to_string(env::args().nth(1).expect("Expected file argument")).expect("Failed to read file");

    match parser().parse(src.trim().chars()) {
        Ok(json) => println!("{:#?}", json),
        Err(errs) => errs
            .into_iter()
            .for_each(|e| println!("{}", e)),
    }
}
