#![allow(clippy::result_large_err, clippy::type_complexity)]

use criterion::{black_box, criterion_group, criterion_main, Criterion};

mod utils;

#[derive(Debug, Clone, PartialEq)]
pub enum Json {
    Null,
    Bool(bool),
    Str(String),
    Num(f64),
    Array(Vec<Json>),
    Object(Vec<(String, Json)>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum JsonZero<'a> {
    Null,
    Bool(bool),
    Str(&'a [u8]),
    Num(f64),
    Array(Vec<JsonZero<'a>>),
    Object(Vec<(&'a [u8], JsonZero<'a>)>),
}

static JSON: &[u8] = include_bytes!("samples/sample.json");

fn bench_json(c: &mut Criterion) {
    c.bench_function("json_nom", {
        move |b| b.iter(|| black_box(nom::json(black_box(JSON)).unwrap()))
    });

    c.bench_function("json_nom8", {
        move |b| b.iter(|| black_box(nom8::json(black_box(JSON)).unwrap()))
    });

    c.bench_function("json_winnow", {
        move |b| {
            b.iter(|| {
                let mut input = black_box(JSON);
                black_box(winnow::json(&mut input).unwrap())
            })
        }
    });

    c.bench_function("json_chumsky", {
        use ::chumsky::prelude::*;
        let json = chumsky_zero_copy::json::<EmptyErr>();
        move |b| {
            b.iter(|| {
                black_box(json.parse(black_box(JSON)))
                    .into_result()
                    .unwrap()
            })
        }
    });

    c.bench_function("json_chumsky_check", {
        use ::chumsky::prelude::*;
        let json = chumsky_zero_copy::json::<EmptyErr>();
        move |b| {
            b.iter(|| {
                assert!(black_box(json.check(black_box(JSON)))
                    .into_errors()
                    .is_empty())
            })
        }
    });

    c.bench_function("json_chumsky_rich", {
        use ::chumsky::prelude::*;
        let json = chumsky_zero_copy::json::<Rich<u8>>();
        move |b| {
            b.iter(|| {
                black_box(json.parse(black_box(JSON)))
                    .into_result()
                    .unwrap()
            })
        }
    });

    c.bench_function("json_chumsky_check_rich", {
        use ::chumsky::prelude::*;
        let json = chumsky_zero_copy::json::<Rich<u8>>();
        move |b| {
            b.iter(|| {
                assert!(black_box(json.check(black_box(JSON)))
                    .into_errors()
                    .is_empty())
            })
        }
    });

    c.bench_function("json_serde_json", {
        use serde_json::{from_slice, Value};
        move |b| b.iter(|| black_box(from_slice::<Value>(black_box(JSON)).unwrap()))
    });

    c.bench_function("json_pom", {
        let json = pom::json();
        move |b| b.iter(|| black_box(json.parse(black_box(JSON)).unwrap()))
    });

    c.bench_function("json_pest", {
        let json = black_box(std::str::from_utf8(JSON).unwrap());
        move |b| b.iter(|| black_box(pest::parse(json).unwrap()))
    });

    c.bench_function("json_sn", {
        move |b| b.iter(|| black_box(sn::Parser::new(black_box(JSON)).parse().unwrap()))
    });
}

criterion_group!(
    name = benches;
    config = utils::make_criterion();
    targets = bench_json
);

criterion_main!(benches);

mod chumsky_zero_copy {
    use chumsky::{error::Error, prelude::*};

    use super::JsonZero;
    use std::str;

    pub fn json<'a, E: Error<'a, &'a [u8]> + 'a>(
    ) -> impl Parser<'a, &'a [u8], JsonZero<'a>, extra::Err<E>> {
        recursive(|value| {
            let digits = one_of(b'0'..=b'9').repeated();

            let int = one_of(b'1'..=b'9')
                .then(one_of(b'0'..=b'9').repeated())
                .ignored()
                .or(just(b'0').ignored())
                .ignored();

            let frac = just(b'.').then(digits.clone());

            let exp = one_of(b"eE")
                .then(one_of(b"+-").or_not())
                .then(digits.clone());

            let number = just(b'-')
                .or_not()
                .then(int)
                .then(frac.or_not())
                .then(exp.or_not())
                .to_slice()
                .map(|bytes| str::from_utf8(bytes).unwrap().parse().unwrap());

            let escape = just(b'\\').then_ignore(one_of(b"\\/\"bfnrt"));

            let string = none_of(b"\\\"")
                .or(escape)
                .repeated()
                .to_slice()
                .delimited_by(just(b'"'), just(b'"'));

            let array = value
                .clone()
                .separated_by(just(b','))
                .collect()
                .padded()
                .delimited_by(just(b'['), just(b']'));

            let member = string.then_ignore(just(b':').padded()).then(value);
            let object = member
                .clone()
                .separated_by(just(b',').padded())
                .collect()
                .padded()
                .delimited_by(just(b'{'), just(b'}'));

            choice((
                just(b"null").to(JsonZero::Null),
                just(b"true").to(JsonZero::Bool(true)),
                just(b"false").to(JsonZero::Bool(false)),
                number.map(JsonZero::Num),
                string.map(JsonZero::Str),
                array.map(JsonZero::Array),
                object.map(JsonZero::Object),
            ))
            .padded()
        })
    }
}

mod pom {
    use pom::parser::*;
    use pom::Parser;

    use super::Json;
    use std::str::{self, FromStr};

    fn space() -> Parser<u8, ()> {
        one_of(b" \t\r\n").repeat(0..).discard()
    }

    fn number() -> Parser<u8, f64> {
        let integer = (one_of(b"123456789") - one_of(b"0123456789").repeat(0..)) | sym(b'0');
        let frac = sym(b'.') + one_of(b"0123456789").repeat(1..);
        let exp = one_of(b"eE") + one_of(b"+-").opt() + one_of(b"0123456789").repeat(1..);
        let number = sym(b'-').opt() + integer + frac.opt() + exp.opt();
        number
            .collect()
            .convert(str::from_utf8)
            .convert(f64::from_str)
    }

    fn string() -> Parser<u8, String> {
        let special_char = sym(b'\\')
            | sym(b'/')
            | sym(b'"')
            | sym(b'b').map(|_| b'\x08')
            | sym(b'f').map(|_| b'\x0C')
            | sym(b'n').map(|_| b'\n')
            | sym(b'r').map(|_| b'\r')
            | sym(b't').map(|_| b'\t');
        let escape_sequence = sym(b'\\') * special_char;
        let string = sym(b'"') * (none_of(b"\\\"") | escape_sequence).repeat(0..) - sym(b'"');
        string.convert(String::from_utf8)
    }

    fn array() -> Parser<u8, Vec<Json>> {
        let elems = list(call(value), sym(b',') * space());
        sym(b'[') * space() * elems - sym(b']')
    }

    fn object() -> Parser<u8, Vec<(String, Json)>> {
        let member = string() - space() - sym(b':') - space() + call(value);
        let members = list(member, sym(b',') * space());
        let obj = sym(b'{') * space() * members - sym(b'}');
        obj.map(|members| members.into_iter().collect::<Vec<_>>())
    }

    fn value() -> Parser<u8, Json> {
        (seq(b"null").map(|_| Json::Null)
            | seq(b"true").map(|_| Json::Bool(true))
            | seq(b"false").map(|_| Json::Bool(false))
            | number().map(Json::Num)
            | string().map(Json::Str)
            | array().map(Json::Array)
            | object().map(Json::Object))
            - space()
    }

    pub fn json() -> Parser<u8, Json> {
        space() * value() - end()
    }
}

mod nom {
    use nom::{
        branch::alt,
        bytes::complete::{escaped, tag, take_while},
        character::complete::{char, digit0, digit1, none_of, one_of},
        combinator::{cut, map, opt, recognize, value as to},
        error::ParseError,
        multi::separated_list0,
        sequence::{preceded, separated_pair, terminated, tuple},
        IResult,
    };

    use super::JsonZero;
    use std::str;

    fn space<'a, E: ParseError<&'a [u8]>>(i: &'a [u8]) -> IResult<&'a [u8], &'a [u8], E> {
        take_while(|c| b" \t\r\n".contains(&c))(i)
    }

    fn number<'a, E: ParseError<&'a [u8]>>(i: &'a [u8]) -> IResult<&'a [u8], f64, E> {
        map(
            recognize(tuple((
                opt(char('-')),
                alt((
                    to((), tuple((one_of("123456789"), digit0))),
                    to((), char('0')),
                )),
                opt(tuple((char('.'), digit1))),
                opt(tuple((one_of("eE"), opt(one_of("+-")), cut(digit1)))),
            ))),
            |bytes| str::from_utf8(bytes).unwrap().parse::<f64>().unwrap(),
        )(i)
    }

    fn string<'a, E: ParseError<&'a [u8]>>(i: &'a [u8]) -> IResult<&'a [u8], &'a [u8], E> {
        preceded(
            char('"'),
            cut(terminated(
                escaped(none_of("\\\""), '\\', one_of("\\/\"bfnrt")),
                char('"'),
            )),
        )(i)
    }

    fn array<'a, E: ParseError<&'a [u8]>>(i: &'a [u8]) -> IResult<&'a [u8], Vec<JsonZero<'a>>, E> {
        preceded(
            char('['),
            cut(terminated(
                separated_list0(preceded(space, char(',')), value),
                preceded(space, char(']')),
            )),
        )(i)
    }

    fn member<'a, E: ParseError<&'a [u8]>>(
        i: &'a [u8],
    ) -> IResult<&'a [u8], (&'a [u8], JsonZero<'a>), E> {
        separated_pair(
            preceded(space, string),
            cut(preceded(space, char(':'))),
            value,
        )(i)
    }

    fn object<'a, E: ParseError<&'a [u8]>>(
        i: &'a [u8],
    ) -> IResult<&'a [u8], Vec<(&'a [u8], JsonZero<'a>)>, E> {
        preceded(
            char('{'),
            cut(terminated(
                separated_list0(preceded(space, char(',')), member),
                preceded(space, char('}')),
            )),
        )(i)
    }

    fn value<'a, E: ParseError<&'a [u8]>>(i: &'a [u8]) -> IResult<&'a [u8], JsonZero<'a>, E> {
        preceded(
            space,
            alt((
                to(JsonZero::Null, tag("null")),
                to(JsonZero::Bool(true), tag("true")),
                to(JsonZero::Bool(false), tag("false")),
                map(number, JsonZero::Num),
                map(string, JsonZero::Str),
                map(array, JsonZero::Array),
                map(object, JsonZero::Object),
            )),
        )(i)
    }

    fn root<'a, E: ParseError<&'a [u8]>>(i: &'a [u8]) -> IResult<&'a [u8], JsonZero<'a>, E> {
        terminated(value, space)(i)
    }

    pub fn json(i: &[u8]) -> IResult<&[u8], JsonZero<'_>, (&[u8], nom::error::ErrorKind)> {
        root(i)
    }
}

mod nom8 {
    use nom8::{
        branch::alt,
        bytes::{escaped, tag},
        character::{char, complete::digit0, digit1, multispace0, none_of, one_of},
        combinator::{cut, map, opt, recognize, value as to},
        error::ParseError,
        multi::separated_list0,
        sequence::{preceded, separated_pair, terminated},
        IResult, Parser,
    };

    use super::JsonZero;
    use std::str;

    fn space<'a, E: ParseError<&'a [u8]>>(i: &'a [u8]) -> IResult<&'a [u8], &'a [u8], E> {
        multispace0().parse_complete(i)
    }

    fn number<'a, E: ParseError<&'a [u8]>>(i: &'a [u8]) -> IResult<&'a [u8], f64, E> {
        map(
            recognize((
                opt(char('-')),
                alt((to((), (one_of("123456789"), digit0)), to((), char('0')))),
                opt((char('.'), digit1())),
                opt((one_of("eE"), opt(one_of("+-")), cut(digit1()))),
            )),
            |bytes| str::from_utf8(bytes).unwrap().parse::<f64>().unwrap(),
        )
        .parse_complete(i)
    }

    fn string<'a, E: ParseError<&'a [u8]>>(i: &'a [u8]) -> IResult<&'a [u8], &'a [u8], E> {
        preceded(
            char('"'),
            cut(terminated(
                escaped(none_of("\\\""), '\\', one_of("\\/\"bfnrt")),
                char('"'),
            )),
        )
        .parse_complete(i)
    }

    fn array<'a, E: ParseError<&'a [u8]>>(i: &'a [u8]) -> IResult<&'a [u8], Vec<JsonZero<'a>>, E> {
        preceded(
            char('['),
            cut(terminated(
                separated_list0(preceded(space, char(',')), value),
                preceded(space, char(']')),
            )),
        )
        .parse_complete(i)
    }

    fn member<'a, E: ParseError<&'a [u8]>>(
        i: &'a [u8],
    ) -> IResult<&'a [u8], (&'a [u8], JsonZero<'a>), E> {
        separated_pair(
            preceded(space, string),
            cut(preceded(space, char(':'))),
            value,
        )
        .parse_complete(i)
    }

    fn object<'a, E: ParseError<&'a [u8]>>(
        i: &'a [u8],
    ) -> IResult<&'a [u8], Vec<(&'a [u8], JsonZero<'a>)>, E> {
        preceded(
            char('{'),
            cut(terminated(
                separated_list0(preceded(space, char(',')), member),
                preceded(space, char('}')),
            )),
        )
        .parse_complete(i)
    }

    fn value<'a, E: ParseError<&'a [u8]>>(i: &'a [u8]) -> IResult<&'a [u8], JsonZero<'a>, E> {
        preceded(
            space,
            alt((
                to(JsonZero::Null, tag("null")),
                to(JsonZero::Bool(true), tag("true")),
                to(JsonZero::Bool(false), tag("false")),
                map(number, JsonZero::Num),
                map(string, JsonZero::Str),
                map(array, JsonZero::Array),
                map(object, JsonZero::Object),
            )),
        )
        .parse_complete(i)
    }

    fn root<'a, E: ParseError<&'a [u8]>>(i: &'a [u8]) -> IResult<&'a [u8], JsonZero<'a>, E> {
        terminated(value, space).parse_complete(i)
    }

    pub fn json(i: &[u8]) -> IResult<&[u8], JsonZero<'_>, (&[u8], nom8::error::ErrorKind)> {
        root(i)
    }
}

mod winnow {
    use winnow::{
        ascii::{digit0, digit1, take_escaped},
        combinator::separated,
        combinator::{alt, dispatch},
        combinator::{fail, opt, peek},
        combinator::{preceded, separated_pair, terminated},
        error::{EmptyError, ParserError},
        prelude::*,
        token::{any, none_of, one_of, take_while},
        Result,
    };

    use super::JsonZero;
    use std::str;

    fn space<'a, E: ParserError<&'a [u8]>>(i: &mut &'a [u8]) -> Result<&'a [u8], E> {
        take_while(0.., [b' ', b'\t', b'\r', b'\n']).parse_next(i)
    }

    fn number<'a, E: ParserError<&'a [u8]>>(i: &mut &'a [u8]) -> Result<f64, E> {
        (
            opt('-'),
            alt(((one_of(b'1'..=b'9'), digit0).void(), one_of('0').void())),
            opt(('.', digit1)),
            opt((one_of([b'e', b'E']), opt(one_of([b'+', b'-'])), digit1)),
        )
            .take()
            .map(|bytes| str::from_utf8(bytes).unwrap().parse::<f64>().unwrap())
            .parse_next(i)
    }

    fn string<'a, E: ParserError<&'a [u8]>>(i: &mut &'a [u8]) -> Result<&'a [u8], E> {
        preceded(
            '"',
            terminated(
                take_escaped(
                    none_of([b'\\', b'"']),
                    '\\',
                    one_of([b'\\', b'/', b'"', b'b', b'f', b'n', b'r', b't']),
                ),
                '"',
            ),
        )
        .parse_next(i)
    }

    fn array<'a, E: ParserError<&'a [u8]>>(i: &mut &'a [u8]) -> Result<Vec<JsonZero<'a>>, E> {
        preceded(
            '[',
            terminated(
                separated(0.., value, preceded(space, ',')),
                preceded(space, ']'),
            ),
        )
        .parse_next(i)
    }

    fn member<'a, E: ParserError<&'a [u8]>>(
        i: &mut &'a [u8],
    ) -> Result<(&'a [u8], JsonZero<'a>), E> {
        separated_pair(preceded(space, string), preceded(space, ':'), value).parse_next(i)
    }

    fn object<'a, E: ParserError<&'a [u8]>>(
        i: &mut &'a [u8],
    ) -> Result<Vec<(&'a [u8], JsonZero<'a>)>, E> {
        preceded(
            '{',
            terminated(
                separated(0.., member, preceded(space, ',')),
                preceded(space, '}'),
            ),
        )
        .parse_next(i)
    }

    fn value<'a, E: ParserError<&'a [u8]>>(i: &mut &'a [u8]) -> Result<JsonZero<'a>, E> {
        preceded(
            space,
            dispatch!(peek(any);
                b'n' => "null".value(JsonZero::Null),
                b't' => "true".value(JsonZero::Bool(true)),
                b'f' => "false".value(JsonZero::Bool(false)),
                b'+' | b'-' | b'0'..=b'9' => number.map(JsonZero::Num),
                b'"' => string.map(JsonZero::Str),
                b'[' => array.map(JsonZero::Array),
                b'{' => object.map(JsonZero::Object),
                _ => fail,
            ),
        )
        .parse_next(i)
    }

    fn root<'a, E: ParserError<&'a [u8]>>(i: &mut &'a [u8]) -> Result<JsonZero<'a>, E> {
        terminated(value, space).parse_next(i)
    }

    pub fn json<'a>(i: &mut &'a [u8]) -> Result<JsonZero<'a>, EmptyError> {
        root.parse_next(i)
    }
}

#[allow(clippy::empty_docs)] // TODO: Remove, pest does things clippy doesn't like for some reason
mod pest {
    use super::JsonZero;

    use pest::{error::Error, Parser};

    #[derive(pest_derive::Parser)]
    #[grammar = "benches/json.pest"]
    struct JsonParser;

    pub fn parse(file: &str) -> Result<JsonZero<'_>, Error<Rule>> {
        let json = JsonParser::parse(Rule::json, file)?.next().unwrap();

        use pest::iterators::Pair;

        fn parse_value(pair: Pair<Rule>) -> JsonZero {
            match pair.as_rule() {
                Rule::object => JsonZero::Object(
                    pair.into_inner()
                        .map(|pair| {
                            let mut inner_rules = pair.into_inner();
                            let name = inner_rules
                                .next()
                                .unwrap()
                                .into_inner()
                                .next()
                                .unwrap()
                                .as_str();
                            let value = parse_value(inner_rules.next().unwrap());
                            (name.as_bytes(), value)
                        })
                        .collect(),
                ),
                Rule::array => JsonZero::Array(pair.into_inner().map(parse_value).collect()),
                Rule::string => {
                    JsonZero::Str(pair.into_inner().next().unwrap().as_str().as_bytes())
                }
                Rule::number => JsonZero::Num(pair.as_str().parse().unwrap()),
                Rule::boolean => JsonZero::Bool(pair.as_str().parse().unwrap()),
                Rule::null => JsonZero::Null,
                Rule::json
                | Rule::EOI
                | Rule::pair
                | Rule::value
                | Rule::inner
                | Rule::char
                | Rule::WHITESPACE => unreachable!(),
            }
        }

        Ok(parse_value(json))
    }
}
