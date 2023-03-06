//! This is a parser for JSON.
//! Run it with the following command:
//! cargo run --example json -- examples/sample.json

use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};
use chumsky::{error::RichReason, prelude::*};
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

fn parser<'a>() -> impl Parser<'a, &'a str, Json, extra::Err<Rich<'a, char>>> {
    recursive(|value| {
        let digits = text::digits(10).slice();

        let frac = just('.').then(digits.clone());

        let exp = just('e')
            .or(just('E'))
            .then(one_of("+-").or_not())
            .then(digits.clone());

        let number = just('-')
            .or_not()
            .then(text::int(10))
            .then(frac.or_not())
            .then(exp.or_not())
            .map_slice(|s: &str| s.parse().unwrap())
            .boxed();

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
                just('u').ignore_then(text::digits(16).exactly(4).slice().validate(
                    |digits, span, emitter| {
                        char::from_u32(u32::from_str_radix(digits, 16).unwrap()).unwrap_or_else(
                            || {
                                emitter.emit(Rich::custom(span, "invalid unicode character"));
                                '\u{FFFD}' // unicode replacement character
                            },
                        )
                    },
                )),
            )))
            .ignored()
            .boxed();

        let string = none_of("\\\"")
            .ignored()
            .or(escape)
            .repeated()
            .slice()
            .map(ToString::to_string)
            .delimited_by(just('"'), just('"'))
            .boxed();

        let array = value
            .clone()
            .separated_by(just(',').padded().recover_with(skip_then_retry_until(
                any().ignored(),
                one_of(",").ignored(),
            )))
            .allow_trailing()
            .collect()
            .padded()
            .delimited_by(
                just('['),
                just(']')
                    .ignored()
                    .recover_with(via_parser(end()))
                    .recover_with(skip_then_retry_until(any().ignored(), end())),
            )
            .boxed();

        let member = string.clone().then_ignore(just(':').padded()).then(value);
        let object = member
            .clone()
            .separated_by(just(',').padded().recover_with(skip_then_retry_until(
                any().ignored(),
                one_of(",").ignored(),
            )))
            .collect()
            .padded()
            .delimited_by(
                just('{'),
                just('}')
                    .ignored()
                    .recover_with(via_parser(end()))
                    .recover_with(skip_then_retry_until(any().ignored(), end())),
            )
            .boxed();

        choice((
            just("null").to(Json::Null),
            just("true").to(Json::Bool(true)),
            just("false").to(Json::Bool(false)),
            number.map(Json::Num),
            string.map(Json::Str),
            array.map(Json::Array),
            object.map(Json::Object),
        ))
        .recover_with(via_parser(nested_delimiters(
            '{',
            '}',
            [('[', ']')],
            |_| Json::Invalid,
        )))
        .recover_with(via_parser(nested_delimiters(
            '[',
            ']',
            [('{', '}')],
            |_| Json::Invalid,
        )))
        .recover_with(skip_then_retry_until(
            any().ignored(),
            one_of(",]}").ignored(),
        ))
        .padded()
    })
}

fn main() {
    let src = fs::read_to_string(env::args().nth(1).expect("Expected file argument"))
        .expect("Failed to read file");

    let (json, errs) = parser().parse(src.trim()).into_output_errors();
    println!("{:#?}", json);
    errs.into_iter().for_each(|e| {
        let msg = match e.reason() {
            RichReason::Custom(msg) => msg.clone(),
            RichReason::ExpectedFound { expected, found } => format!(
                "{}, expected {}",
                if found.is_some() {
                    "Unexpected token"
                } else {
                    "Unexpected end of input"
                },
                if expected.len() == 0 {
                    "something else".to_string()
                } else {
                    expected
                        .into_iter()
                        .map(|expected| expected.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                },
            ),
            RichReason::Many(_) => format!("uhhh"),
        };

        let report = Report::build(ReportKind::Error, (), e.span().start)
            .with_code(3)
            .with_message(msg)
            .with_label(
                Label::new(e.span().into_range())
                    .with_message(match e.reason() {
                        RichReason::Custom(msg) => msg.clone(),
                        RichReason::ExpectedFound { found, .. } => format!(
                            "Unexpected {}",
                            found
                                .as_ref()
                                .map(|c| format!("token {}", c.fg(Color::Red)))
                                .unwrap_or_else(|| "end of input".to_string())
                        ),
                        RichReason::Many(_) => format!("uhhh"),
                    })
                    .with_color(Color::Red),
            );

        // let report = match e.reason() {
        //     RichReason::Unclosed { span, delimiter } => report.with_label(
        //         Label::new(span.clone())
        //             .with_message(format!(
        //                 "Unclosed delimiter {}",
        //                 delimiter.fg(Color::Yellow)
        //             ))
        //             .with_color(Color::Yellow),
        //     ),
        //     RichReason::Unexpected => report,
        //     RichReason::Custom(_) => report,
        // };

        report.finish().print(Source::from(&src)).unwrap();
    });
}
