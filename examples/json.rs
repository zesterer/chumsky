//! This is a parser for JSON.
//! Run it with the following command:
//! cargo run --example json -- examples/sample.json

use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};
use chumsky::zero_copy::prelude::*;
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

fn parser<'a>() -> impl Parser<'a, str, Json, Rich<str>, ()> {
    recursive(|value| {
        let frac = just('.').then_ignore(text::digits(10))
            .map_slice(|x| x);

        let exp = just('e')
            .or(just('E'))
            .then_ignore(just('+').or(just('-')).or_not())
            .then_ignore(text::digits(10))
            .map_slice(|x| x);

        let number = just('-')
            .or_not()
            .then_ignore(text::int(10))
            .then_ignore(frac.or_not())
            .then_ignore(exp.or_not())
            .map_slice(|x| x)
            .from_str()
            .unwrapped();

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
                    any()
                        .filter(|c: &char| c.is_digit(16))
                        .repeated()
                        .exactly(4)
                        .map_slice(|x| x)
                        .try_map(|digits, span| {
                            char::from_u32(u32::from_str_radix(digits, 16).unwrap())
                                .ok_or_else(|| Rich::expected_found(None, None, span))
                        })
                        .recover_with(empty().to('\u{FFFD}')) // unicode replacement character
                        /*.validate(|digits, span, emit| {
                            char::from_u32(u32::from_str_radix(&digits, 16).unwrap())
                                .unwrap_or_else(|| {
                                    emit(Rich::custom(span, "invalid unicode character"));
                                    '\u{FFFD}' // unicode replacement character
                                })
                        }),*/
                )),
        );

        let string = just('"')
            .ignore_then(any().filter(|c| *c != '\\' && *c != '"').or(escape).repeated().collect::<Vec<_>>())
            .then_ignore(just('"'))
            .collect::<String>();

        let array = value
            .clone()
            .chain(just(',').ignore_then(value.clone()).repeated().collect::<Vec<_>>())
            .or_not()
            .flatten()
            .delimited_by(just('['), just(']'))
            .map(Json::Array);

        let member = string.clone().then_ignore(just(':').padded()).then(value);
        let object = member
            .clone()
            .chain(just(',').padded().ignore_then(member).repeated().collect::<Vec<_>>())
            .or_not()
            .flatten()
            .padded()
            .delimited_by(just('{'), just('}'))
            .collect::<HashMap<String, Json>>()
            .map(Json::Object);

        just("null")
            .to(Json::Null)
            .or(just("true").to(Json::Bool(true)))
            .or(just("false").to(Json::Bool(false)))
            .or(number.map(Json::Num))
            .or(string.map(Json::Str))
            .or(array)
            .or(object)
            .recover_with(any().repeated().delimited_by(just('{'), just('}')).to(Json::Invalid))
            .recover_with(any().repeated().delimited_by(just('['), just(']')).to(Json::Invalid))
            .recover_with(take_until(one_of([']', '}'])).to(Json::Invalid))
            .padded()
    })
    .then_ignore(end().recover_with(take_until(end()).to(())))
}

fn main() {
    let src = fs::read_to_string(env::args().nth(1).expect("Expected file argument"))
        .expect("Failed to read file");

    let (json, errs) = parser().parse(src.trim()).into_output_errors();
    println!("{:#?}", json);
    errs.into_iter().for_each(|e| {
        let msg = /*if let chumsky::error::SimpleReason::Custom(msg) = e.reason() {
            msg.clone()
        } else {*/
            format!(
                "{}, expected {}",
                if e.found().is_some() {
                    "Unexpected token"
                } else {
                    "Unexpected end of input"
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
            );
        //};

        let report = Report::build(ReportKind::Error, (), e.span().start)
            .with_code(3)
            .with_message(msg)
            .with_label(
                Label::new(e.span())
                    .with_message(format!(
                        "Unexpected {}",
                        e.found()
                            .map(|c| format!("token {}", c.fg(Color::Red)))
                            .unwrap_or_else(|| "end of input".to_string())
                    ))
                    .with_color(Color::Red),
            );

        // let report = match e.reason() {
        //     chumsky::error::SimpleReason::Unclosed { span, delimiter } => report.with_label(
        //         Label::new(span.clone())
        //             .with_message(format!(
        //                 "Unclosed delimiter {}",
        //                 delimiter.fg(Color::Yellow)
        //             ))
        //             .with_color(Color::Yellow),
        //     ),
        //     chumsky::error::SimpleReason::Unexpected => report,
        //     chumsky::error::SimpleReason::Custom(_) => report,
        // };

        report.finish().print(Source::from(&src)).unwrap();
    });
}
