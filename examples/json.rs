//! This is a parser for JSON.
//! Run it with the following command:
//! cargo run --example json -- examples/sample.json

use chumsky::prelude::*;
use ariadne::{Report, ReportKind, Label, Source, Color, Fmt};
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
            .map(|s| s.parse().unwrap())
            .labelled("number");

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
            .collect::<String>()
            .labelled("string");

        let array = value.clone()
            .chain(just(',').padding_for(value.clone()).repeated())
            .or_not()
            .flatten()
            .delimited_by('[', ']')
            .map(|x| x.unwrap_or_else(Vec::new))
            .labelled("array");

        let member = string.padded_by(just(':').padded()).then(value);
        let object = member.clone()
            .chain(just(',').padded().padding_for(member).repeated())
            .or_not()
            .flatten()
            .padded()
            .delimited_by('{', '}')
            .map(|x| x.unwrap_or_else(Vec::new))
            .collect::<HashMap<String, Json>>()
            .labelled("object");

        seq("null".chars()).to(Json::Null).labelled("null")
            .or(seq("true".chars()).to(Json::Bool(true)).labelled("true"))
            .or(seq("false".chars()).to(Json::Bool(false)).labelled("false"))
            .or(number.map(Json::Num))
            .or(string.map(Json::Str))
            .or(array.map(Json::Array))
            .or(object.map(Json::Object))
            .padded()
    })
}

fn main() {
    let src = fs::read_to_string(env::args().nth(1).expect("Expected file argument")).expect("Failed to read file");

    match parser().parse(src.trim()) {
        Ok(json) => println!("{:#?}", json),
        Err(errs) => errs
            .into_iter()
            .for_each(|e| {
                Report::build(ReportKind::Error, (), e.span().unwrap().start)
                    .with_code(3)
                    .with_message(if e.found().is_some() {
                        "Unexpected token in input"
                    } else {
                        "Unexpected end of input"
                    })
                    .with_label(Label::new(e.span().unwrap())
                        .with_message(format!("Unexpected {}", e
                            .found()
                            .map(|c| format!("token {}", c.fg(Color::Red)))
                            .unwrap_or_else(|| "end of input".to_string())))
                        .with_color(Color::Red))
                    .finish()
                    .print(Source::from(&src))
                    .unwrap();
            }),
    }
}
