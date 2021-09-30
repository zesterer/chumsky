//! This is a parser for JSON.
//! Run it with the following command:
//! cargo run --example json -- examples/sample.json

use chumsky::prelude::*;
use ariadne::{Report, ReportKind, Label, Source, Color, Fmt};
use std::{collections::HashMap, env, fs};

#[derive(Clone, Debug)]
enum Json {
    Invalid,
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
            .ignore_then(just('+').or(just('-')).or_not())
            .chain(text::digits());

        let number = just('-').or_not()
            .chain(text::int())
            .chain(frac.or_not().flatten())
            .chain::<char, _, _>(exp.or_not().flatten())
            .collect::<String>()
            .map(|s| s.parse().unwrap())
            .labelled("number");

        let escape = just('\\')
            .ignore_then(just('\\')
            .or(just('/'))
            .or(just('"'))
            .or(just('b').to('\x08'))
            .or(just('f').to('\x0C'))
            .or(just('n').to('\n'))
            .or(just('r').to('\r'))
            .or(just('t').to('\t')));

        let string = just('"')
            .ignore_then(filter(|c| *c != '\\' && *c != '"').or(escape).repeated())
            .then_ignore(just('"'))
            .collect::<String>()
            .labelled("string");
        // let string = just('@').map(|_| "STRING".to_owned());

        let array = value.clone()
            .chain(just(',').ignore_then(value.clone()).repeated())
            .or_not()
            .flatten()
            .delimited_by('[', ']')
            .map(Json::Array)
            .labelled("array");

        let member = string.then_ignore(just(':').padded()).then(value);
        let object = member.clone()
            .chain(just(',').padded().ignore_then(member).repeated())
            .or_not()
            .flatten()
            .padded()
            .delimited_by('{', '}')
            .collect::<HashMap<String, Json>>()
            .map(Json::Object)
            .labelled("object");

        seq("null".chars()).to(Json::Null).labelled("null")
            .or(seq("true".chars()).to(Json::Bool(true)).labelled("true"))
            .or(seq("false".chars()).to(Json::Bool(false)).labelled("false"))
            .or(number.map(Json::Num))
            .or(string.map(Json::Str))
            .or(array)
            .or(object)
            .recover_with(SkipThenRetryUntil([')', ']']))
            .recover_with(NestedDelimiters('{', '}', || Json::Invalid))
            .recover_with(NestedDelimiters('[', ']', || Json::Invalid))
            .padded()
    })
        .then_ignore(end())
}

fn main() {
    let src = fs::read_to_string(env::args().nth(1).expect("Expected file argument")).expect("Failed to read file");

    let (json, errs) = parser().parse_recovery(src.trim());
    println!("{:#?}", json);
    errs
        .into_iter()
        .for_each(|e| {
            Report::build(ReportKind::Error, (), e.span().start)
                .with_code(3)
                .with_message(format!("{}, expected {}", if e.found().is_some() {
                    "Unexpected token in input"
                } else {
                    "Unexpected end of input"
                }, if e.expected().len() == 0 {
                    "end of input".to_string()
                } else {
                    e.expected().map(|x| x.to_string()).collect::<Vec<_>>().join(", ")
                }))
                .with_label(Label::new(e.span().start..e.span().end)
                    .with_message(format!("Unexpected {}", e
                        .found()
                        .map(|c| format!("token {}", c.fg(Color::Red)))
                        .unwrap_or_else(|| "end of input".to_string())))
                    .with_color(Color::Red))
                .finish()
                .print(Source::from(&src))
                .unwrap();
        });
}
