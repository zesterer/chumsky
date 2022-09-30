//! This is a parser for JSON.
//! Run it with the following command:
//! cargo run --example json -- examples/sample.json

use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};
use chumsky::prelude::*;
use std::{collections::HashMap, env, fs};

#[derive(Clone, Debug)]
enum Json {
    Invalid,
    Null,
    Bool(bool),
    Str(String),
    Num(f64),
    Array(Vec<Json>),
    Object(HashMap<String, Json>),
}

fn parser() -> impl Parser<char, Json, Error = Simple<char>> {
    recursive(|value| {
        let frac = just('.').chain(text::digits(10));

        let exp = just('e')
            .or(just('E'))
            .chain(just('+').or(just('-')).or_not())
            .chain::<char, _, _>(text::digits(10));

        let number = just('-')
            .or_not()
            .chain::<char, _, _>(text::int(10))
            .chain::<char, _, _>(frac.or_not().flatten())
            .chain::<char, _, _>(exp.or_not().flatten())
            .collect::<String>()
            .from_str()
            .unwrapped()
            .labelled("number");

        let escape = just('\\').ignore_then(
            just('\\')
                .or(just('/'))
                .or(just('"'))
                .or(just('b').to('\x08'))
                .or(just('f').to('\x0C'))
                .or(just('n').to('\n'))
                .or(just('r').to('\r'))
                .or(just('t').to('\t'))
                .or(just('u').ignore_then(
                    filter(|c: &char| c.is_digit(16))
                        .repeated()
                        .exactly(4)
                        .collect::<String>()
                        .validate(|digits, span, emit| {
                            char::from_u32(u32::from_str_radix(&digits, 16).unwrap())
                                .unwrap_or_else(|| {
                                    emit(Simple::custom(span, "invalid unicode character"));
                                    '\u{FFFD}' // unicode replacement character
                                })
                        }),
                )),
        );

        let string = just('"')
            .ignore_then(filter(|c| *c != '\\' && *c != '"').or(escape).repeated())
            .then_ignore(just('"'))
            .collect::<String>()
            .labelled("string");

        let array = value
            .clone()
            .chain(just(',').ignore_then(value.clone()).repeated())
            .or_not()
            .flatten()
            .delimited_by(just('['), just(']'))
            .map(Json::Array)
            .labelled("array");

        let member = string.clone().then_ignore(just(':').padded()).then(value);
        let object = member
            .clone()
            .chain(just(',').padded().ignore_then(member).repeated())
            .or_not()
            .flatten()
            .padded()
            .delimited_by(just('{'), just('}'))
            .collect::<HashMap<String, Json>>()
            .map(Json::Object)
            .labelled("object");

        just("null")
            .to(Json::Null)
            .labelled("null")
            .or(just("true").to(Json::Bool(true)).labelled("true"))
            .or(just("false").to(Json::Bool(false)).labelled("false"))
            .or(number.map(Json::Num))
            .or(string.map(Json::Str))
            .or(array)
            .or(object)
            .recover_with(nested_delimiters('{', '}', [('[', ']')], |_| Json::Invalid))
            .recover_with(nested_delimiters('[', ']', [('{', '}')], |_| Json::Invalid))
            .recover_with(skip_then_retry_until(['}', ']']))
            .padded()
    })
    .then_ignore(end().recover_with(skip_then_retry_until([])))
}

fn main() {
    let src = fs::read_to_string(env::args().nth(1).expect("Expected file argument"))
        .expect("Failed to read file");

    let (json, errs) = parser().parse_recovery(src.trim());
    println!("{:#?}", json);
    errs.into_iter().for_each(|e| {
        let msg = if let chumsky::error::SimpleReason::Custom(msg) = e.reason() {
            msg.clone()
        } else {
            format!(
                "{}{}, expected {}",
                if e.found().is_some() {
                    "Unexpected token"
                } else {
                    "Unexpected end of input"
                },
                if let Some(label) = e.label() {
                    format!(" while parsing {}", label)
                } else {
                    String::new()
                },
                if e.expected().len() == 0 {
                    "something else".to_string()
                } else {
                    e.expected()
                        .map(|expected| match expected {
                            Some(expected) => expected.to_string(),
                            None => "end of input".to_string(),
                        })
                        .collect::<Vec<_>>()
                        .join(", ")
                },
            )
        };

        let report = Report::build(ReportKind::Error, (), e.span().start)
            .with_code(3)
            .with_message(msg)
            .with_label(
                Label::new(e.span())
                    .with_message(match e.reason() {
                        chumsky::error::SimpleReason::Custom(msg) => msg.clone(),
                        _ => format!(
                            "Unexpected {}",
                            e.found()
                                .map(|c| format!("token {}", c.fg(Color::Red)))
                                .unwrap_or_else(|| "end of input".to_string())
                        ),
                    })
                    .with_color(Color::Red),
            );

        let report = match e.reason() {
            chumsky::error::SimpleReason::Unclosed { span, delimiter } => report.with_label(
                Label::new(span.clone())
                    .with_message(format!(
                        "Unclosed delimiter {}",
                        delimiter.fg(Color::Yellow)
                    ))
                    .with_color(Color::Yellow),
            ),
            chumsky::error::SimpleReason::Unexpected => report,
            chumsky::error::SimpleReason::Custom(_) => report,
        };

        report.finish().print(Source::from(&src)).unwrap();
    });
}
