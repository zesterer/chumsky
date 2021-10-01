//! This is an entire parser and interpreter for a dynamically-typed Rust-like expression-oriented
//! programming language. See `example.nrs` for sample source code.
//! Run it with the following command:
//! cargo run --example nano_rust -- examples/example.nrs

use chumsky::{prelude::*, stream::Stream};
use ariadne::{Report, ReportKind, Label, Source, Color, Fmt};
use std::{collections::HashMap, env, fs, fmt};

pub type Span = std::ops::Range<usize>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Token {
    Null,
    Bool(bool),
    Num(String),
    Str(String),
    Op(String),
    Ctrl(char),
    Ident(String),
    Fn,
    Let,
    Print,
    If,
    Else,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Token::Null => write!(f, "null"),
            Token::Bool(x) => write!(f, "{}", x),
            Token::Num(n) => write!(f, "{}", n),
            Token::Str(s) => write!(f, "{}", s),
            Token::Op(s) => write!(f, "{}", s),
            Token::Ctrl(c) => write!(f, "{}", c),
            Token::Ident(s) => write!(f, "{}", s),
            Token::Fn => write!(f, "fn"),
            Token::Let => write!(f, "let"),
            Token::Print => write!(f, "print"),
            Token::If => write!(f, "if"),
            Token::Else => write!(f, "else"),
        }
    }
}

fn lexer() -> impl Parser<char, Vec<(Token, Span)>, Error = Simple<char>> {
    let num = text::int(10)
        .chain::<char, _, _>(just('.').chain(text::digits(10)).or_not().flatten())
        .collect::<String>()
        .map(Token::Num);

    let str_ = just('"')
        .ignore_then(filter(|c| *c != '"').repeated())
        .then_ignore(just('"'))
        .collect::<String>()
        .map(Token::Str);

    let op = one_of("+-*/!=".chars())
        .repeated_at_least(1)
        .collect::<String>()
        .map(Token::Op);

    let ctrl = one_of("()[]{};,".chars()).map(|c| Token::Ctrl(c));

    let ident = text::ident().collect::<String>().map(|ident| match ident.as_str() {
        "fn" => Token::Fn,
        "let" => Token::Let,
        "print" => Token::Print,
        "if" => Token::If,
        "else" => Token::Else,
        "true" => Token::Bool(true),
        "false" => Token::Bool(false),
        "null" => Token::Null,
        _ => Token::Ident(ident),
    });

    let token = num
        .or(str_)
        .or(op)
        .or(ctrl)
        .or(ident)
        .recover_with(SkipThenRetryUntil([]));

    token
        .map_with_span(|tok, span| (tok, span))
        .padded()
        .repeated()
}

#[derive(Clone, Debug, PartialEq)]
enum Value {
    Null,
    Bool(bool),
    Num(f64),
    Str(String),
    List(Vec<Value>),
    Func(String),
}

impl Value {
    fn num(self) -> f64 {
        if let Value::Num(x) = self {
            x
        } else {
            panic!("Value is not a number!");
        }
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Null => write!(f, "null"),
            Self::Bool(x) => write!(f, "{}", x),
            Self::Num(x) => write!(f, "{}", x),
            Self::Str(x) => write!(f, "{}", x),
            Self::List(xs) => write!(f, "[{}]", xs
                .iter()
                .map(|x| x.to_string())
                .collect::<Vec<_>>()
                .join(", ")),
            Self::Func(name) => write!(f, "<function: {}>", name),
        }
    }
}

#[derive(Clone, Debug)]
enum BinaryOp {
    Add, Sub,
    Mul, Div,
    Eq, NotEq,
}

#[derive(Debug)]
enum Expr {
    Error,
    Value(Value),
    List(Vec<Self>),
    Local(String),
    Let(String, Box<Self>, Box<Self>),
    Then(Box<Self>, Box<Self>),
    Binary(Box<Self>, BinaryOp, Box<Self>),
    Call(Box<Self>, Vec<Self>),
    If(Box<Self>, Box<Self>, Box<Self>),
    Print(Box<Self>),
}

#[derive(Debug)]
struct Func {
    args: Vec<String>,
    body: Expr,
}

fn expr_parser() -> impl Parser<Token, Expr, Error = Simple<Token>> + Clone {
    recursive(|expr| {
        let raw_expr = recursive(|raw_expr| {
            let val = filter_map(|span, tok| match tok {
                Token::Null => Ok(Expr::Value(Value::Null)),
                Token::Bool(x) => Ok(Expr::Value(Value::Bool(x))),
                Token::Num(n) => Ok(Expr::Value(Value::Num(n.parse().unwrap()))),
                Token::Str(s) => Ok(Expr::Value(Value::Str(s))),
                _ => Err(Simple::expected_token_found(span, Vec::new(), Some(tok))),
            })
                .labelled("value");

            let ident = filter_map(|span, tok| match tok {
                Token::Ident(ident) => Ok(ident.clone()),
                _ => Err(Simple::expected_token_found(span, Vec::new(), Some(tok))),
            })
                .labelled("identifier");

            let items = expr.clone()
                .chain(just(Token::Ctrl(',')).ignore_then(expr.clone()).repeated())
                .then_ignore(just(Token::Ctrl(',')).or_not())
                .or_not()
                .map(|item| item.unwrap_or_else(Vec::new));

            let let_ = just(Token::Let)
                .ignore_then(ident)
                .then_ignore(just(Token::Op("=".to_string())))
                .then(raw_expr)
                .then_ignore(just(Token::Ctrl(';')))
                .then(expr.clone())
                .map(|((name, val), body)| Expr::Let(name, Box::new(val), Box::new(body)));

            let list = items.clone()
                .delimited_by(Token::Ctrl('['), Token::Ctrl(']'))
                .map(Expr::List);

            let atom = expr.clone().delimited_by(Token::Ctrl('('), Token::Ctrl(')'))
                .or(val)
                .or(just(Token::Print)
                    .ignore_then(expr.clone().delimited_by(Token::Ctrl('('), Token::Ctrl(')')))
                    .map(|expr| Expr::Print(Box::new(expr))))
                .or(let_)
                .or(ident.map(Expr::Local))
                .or(list)
                .or(expr.clone()
                    .delimited_by(Token::Ctrl('('), Token::Ctrl(')')))
                .recover_with(nested_delimiters(
                    Token::Ctrl('('), Token::Ctrl(')'),
                    [
                        (Token::Ctrl('{'), Token::Ctrl('}')),
                        (Token::Ctrl('['), Token::Ctrl(']')),
                    ],
                    || Expr::Error,
                ));

            let call = atom.then(items
                    .delimited_by(Token::Ctrl('('), Token::Ctrl(')'))
                    .repeated())
                .foldl(|f, args| Expr::Call(Box::new(f), args));

            let op = just(Token::Op("*".to_string())).to(BinaryOp::Mul).or(just(Token::Op("/".to_string())).to(BinaryOp::Div));
            let product = call.clone().then(op.then(call).repeated())
                .foldl(|a, (op, b)| Expr::Binary(Box::new(a), op, Box::new(b)));

            let op = just(Token::Op("+".to_string())).to(BinaryOp::Add).or(just(Token::Op("-".to_string())).to(BinaryOp::Sub));
            let sum = product.clone().then(op.then(product).repeated())
                .foldl(|a, (op, b)| Expr::Binary(Box::new(a), op, Box::new(b)));

            let op = just(Token::Op("==".to_string())).to(BinaryOp::Eq).or(just(Token::Op("!=".to_string())).to(BinaryOp::NotEq));
            let compare = sum.clone().then(op.then(sum).repeated())
                .foldl(|a, (op, b)| Expr::Binary(Box::new(a), op, Box::new(b)));

            compare
        });
            // .labelled("expression");

        let block = expr.clone()
            .delimited_by(Token::Ctrl('{'), Token::Ctrl('}'))
            .recover_with(nested_delimiters(
                Token::Ctrl('{'), Token::Ctrl('}'),
                [
                    (Token::Ctrl('('), Token::Ctrl(')')),
                    (Token::Ctrl('['), Token::Ctrl(']')),
                ],
                || Expr::Error,
            ));

        let if_ = recursive(|if_| {
            just(Token::If)
                .ignore_then(expr.clone())
                .then(block.clone())
                .then(just(Token::Else).ignore_then(block.clone().or(if_)).or_not())
                .map(|((cond, a), b)| Expr::If(Box::new(cond), Box::new(a), Box::new(match b {
                    Some(b) => b,
                    None => Expr::Value(Value::Null),
                })))
        });

        let block_expr = block
            .or(if_)
            .labelled("block");

        let block_chain = block_expr.clone().then(block_expr.clone().repeated())
            .foldl(|a, b| Expr::Then(Box::new(a), Box::new(b)));

        block_chain.or(raw_expr.clone())
            .then(just(Token::Ctrl(';')).ignore_then(expr.or_not()).repeated())
            .foldl(|a, b| Expr::Then(Box::new(a), Box::new(match b {
                Some(b) => b,
                None => Expr::Value(Value::Null),
            })))
    })
}

fn funcs_parser() -> impl Parser<Token, HashMap<String, Func>, Error = Simple<Token>> + Clone {
    let ident = filter_map(|span, tok| match tok {
        Token::Ident(ident) => Ok(ident.clone()),
        _ => Err(Simple::expected_token_found(span, Vec::new(), Some(tok))),
    });

    let args = ident.clone()
        .chain(just(Token::Ctrl(',')).ignore_then(ident.clone()).repeated())
        .then_ignore(just(Token::Ctrl(',')).or_not())
        .or_not()
        .map(|items| items.unwrap_or_else(Vec::new))
        .labelled("function args");

    let func = just(Token::Fn)
        .ignore_then(ident.labelled("function name"))
        .then(args.delimited_by(Token::Ctrl('('), Token::Ctrl(')')))
        .then(expr_parser()
            .delimited_by(Token::Ctrl('{'), Token::Ctrl('}'))
            .recover_with(nested_delimiters(
                Token::Ctrl('{'), Token::Ctrl('}'),
                [
                    (Token::Ctrl('('), Token::Ctrl(')')),
                    (Token::Ctrl('['), Token::Ctrl(']')),
                ],
                || Expr::Error,
            )))
        .map(|((name, args), body)| (name, Func {
            args,
            body,
        }))
        .labelled("function");

    func
        .repeated()
        .map(|fs| {
            let mut funcs = HashMap::new();
            for (name, f) in fs {
                if funcs.insert(name.clone(), f).is_some() {
                    panic!("Duplicate function '{}'", name);
                }
            }
            funcs
        })
        .then_ignore(end())
}

fn eval_expr(expr: &Expr, funcs: &HashMap<String, Func>, stack: &mut Vec<(String, Value)>) -> Value {
    match expr {
        Expr::Error => unreachable!(),
        Expr::Value(val) => val.clone(),
        Expr::List(items) => Value::List(items
            .iter()
            .map(|item| eval_expr(item, funcs, stack))
            .collect()),
        Expr::Local(name) => stack
            .iter()
            .rev()
            .find(|(l, _)| l == name)
            .map(|(_, v)| v.clone())
            .or_else(|| Some(Value::Func(name.clone())).filter(|_| funcs.contains_key(name)))
            .unwrap_or_else(|| panic!("No such local '{}' in scope!", name)),
        Expr::Let(local, val, body) => {
            let val = eval_expr(val, funcs, stack);
            stack.push((local.clone(), val));
            let res = eval_expr(body, funcs, stack);
            stack.pop();
            res
        },
        Expr::Then(a, b) => {
            eval_expr(a, funcs, stack);
            eval_expr(b, funcs, stack)
        },
        Expr::Binary(a, BinaryOp::Add, b) => Value::Num(eval_expr(a, funcs, stack).num() + eval_expr(b, funcs, stack).num()),
        Expr::Binary(a, BinaryOp::Sub, b) => Value::Num(eval_expr(a, funcs, stack).num() - eval_expr(b, funcs, stack).num()),
        Expr::Binary(a, BinaryOp::Mul, b) => Value::Num(eval_expr(a, funcs, stack).num() * eval_expr(b, funcs, stack).num()),
        Expr::Binary(a, BinaryOp::Div, b) => Value::Num(eval_expr(a, funcs, stack).num() / eval_expr(b, funcs, stack).num()),
        Expr::Binary(a, BinaryOp::Eq, b) => Value::Bool(eval_expr(a, funcs, stack) == eval_expr(b, funcs, stack)),
        Expr::Binary(a, BinaryOp::NotEq, b) => Value::Bool(eval_expr(a, funcs, stack) != eval_expr(b, funcs, stack)),
        Expr::Call(f, args) => {
            let f = eval_expr(f, funcs, stack);
            match f {
                Value::Func(name) => {
                    let f = &funcs[&name];
                    let mut stack = if f.args.len() != args.len() {
                        panic!("'{}' called with wrong number of arguments (expected {}, found {})", name, f.args.len(), args.len());
                    } else {
                        f.args
                            .iter()
                            .zip(args.iter())
                            .map(|(name, arg)| (name.clone(), eval_expr(arg, funcs, stack)))
                            .collect()
                    };
                    eval_expr(&f.body, funcs, &mut stack)
                },
                f => panic!("{:?} is not callable", f),
            }
        },
        Expr::If(cond, a, b) => {
            let cond = eval_expr(cond, funcs, stack);
            if cond == Value::Bool(true) {
                eval_expr(a, funcs, stack)
            } else {
                eval_expr(b, funcs, stack)
            }
        },
        Expr::Print(a) => {
            let val = eval_expr(a, funcs, stack);
            println!("{}", val);
            val
        },
    }
}

fn main() {
    let src = fs::read_to_string(env::args().nth(1).expect("Expected file argument")).expect("Failed to read file");

    let (tokens, errs) = lexer().parse_recovery(src.as_str());

    let parse_errs = if let Some(tokens) = tokens {
        // println!("Tokens = {:?}", tokens);
        let len = src.chars().count();
        let (ast, parse_errs) = funcs_parser().parse_recovery(Stream::from_iter((), len..len + 1, tokens.into_iter()));

        println!("{:#?}", ast);
        if let Some(funcs) = ast.filter(|_| errs.len() + parse_errs.len() == 0) {
            if let Some(main) = funcs.get("main") {
                assert_eq!(main.args.len(), 0);
                println!("Return value: {}", eval_expr(&main.body, &funcs, &mut Vec::new()));
            } else {
                panic!("No main function!");
            }
        }

        parse_errs
    } else {
        Vec::new()
    };

    errs
        .into_iter()
        .map(|e| e.map(|c| c.to_string()))
        .chain(parse_errs
            .into_iter()
            .map(|e| e.map(|tok| tok.to_string())))
        .for_each(|e| {
            let report = Report::build(ReportKind::Error, (), e.span().start)
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
                    .with_color(Color::Red));

            let report = match e.reason() {
                Some(chumsky::error::SimpleReason::Unclosed(span, c)) => report
                    .with_label(Label::new(span.clone())
                        .with_message(format!("Unclosed delimiter {}", c.fg(Color::Yellow)))
                    .with_color(Color::Yellow)),
                None => report
            };

            report
                .finish()
                .print(Source::from(&src))
                .unwrap();
        });
}
