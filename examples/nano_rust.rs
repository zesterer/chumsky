//! This is an entire parser and interpreter for a dynamically-typed Rust-like expression-oriented
//! programming language. See `example.nrs` for sample source code.
//! Run it with the following command:
//! cargo run --example nano_rust -- examples/example.nrs

use chumsky::prelude::*;
use std::{collections::HashMap, env, fs};

pub type Span = std::ops::Range<usize>;

#[derive(Clone, Debug, PartialEq)]
enum Token {
    Value(Value),
    Op(String),
    Ctrl(char),
    Ident(String),
    Fn,
    Let,
    Print,
    If,
    Else,
}

fn lexer() -> impl Parser<char, Vec<(Token, Span)>, Error = Simple<char>> {
    let num = text::int()
        .chain::<char, _, _>(just('.').chain(text::digits()).or_not().flatten())
        .collect::<String>()
        .map(|s| Token::Value(Value::Num(s.parse().unwrap())));

    let str_ = just('"')
        .padding_for(filter(|c| *c != '"').repeated())
        .padded_by(just('"'))
        .collect::<String>()
        .map(|s| Token::Value(Value::Str(s)));

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
        "true" => Token::Value(Value::Bool(true)),
        "false" => Token::Value(Value::Bool(false)),
        "null" => Token::Value(Value::Null),
        _ => Token::Ident(ident),
    });

    let token = num.or(str_).or(op).or(ctrl).or(ident);

    token
        .map_with_span(|tok, span| (tok, span.unwrap()))
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
                Token::Value(v) => Ok(Expr::Value(v.clone())),
                _ => Err(Simple::expected_token_found(Some(span), Vec::new(), Some(tok))),
            })
                .label("value");

            let ident = filter_map(|span, tok| match tok {
                Token::Ident(ident) => Ok(ident.clone()),
                _ => Err(Simple::expected_token_found(Some(span), Vec::new(), Some(tok))),
            })
                .label("identifier");

            let items = expr.clone()
                .chain(just(Token::Ctrl(',')).padding_for(expr.clone()).repeated())
                .padded_by(just(Token::Ctrl(',')).or_not())
                .or_not()
                .map(|items| items.unwrap_or_else(Vec::new));

            let let_ = just(Token::Let)
                .padding_for(ident)
                .padded_by(just(Token::Op("=".to_string())))
                .then(raw_expr)
                .padded_by(just(Token::Ctrl(';')))
                .then(expr.clone())
                .map(|((name, val), body)| Expr::Let(name, Box::new(val), Box::new(body)));

            let list = items.clone()
                .delimited_by(Token::Ctrl('['), Token::Ctrl(']'))
                .map(|expr| expr.unwrap_or_else(Vec::new))
                .map(Expr::List);

            let atom = expr.clone().delimited_by(Token::Ctrl('('), Token::Ctrl(')'))
                .map(|expr| expr.unwrap_or(Expr::Error))
                .or(val)
                .or(just(Token::Print)
                    .padding_for(expr.clone().delimited_by(Token::Ctrl('('), Token::Ctrl(')')))
                    .map(|expr| expr.unwrap_or(Expr::Error))
                    .map(|expr| Expr::Print(Box::new(expr))))
                .or(let_)
                .or(ident.map(Expr::Local))
                .or(list)
                .or(expr.clone()
                    .delimited_by(Token::Ctrl('('), Token::Ctrl(')'))
                    .map(|expr| expr.unwrap_or(Expr::Error)));

            let call = atom.then(items
                    .delimited_by(Token::Ctrl('('), Token::Ctrl(')'))
                    .map(|expr| expr.unwrap_or_else(Vec::new))
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
                .label("expression")
        });

        let block = expr.clone()
            .delimited_by(Token::Ctrl('{'), Token::Ctrl('}'))
            .map(|expr| expr.unwrap_or(Expr::Error));

        let if_ = recursive(|if_| {
            just(Token::If)
                .padding_for(expr.clone())
                .then(block.clone())
                .then(just(Token::Else).padding_for(block.clone().or(if_)).or_not())
                .map(|((cond, a), b)| Expr::If(Box::new(cond), Box::new(a), Box::new(match b {
                    Some(b) => b,
                    None => Expr::Value(Value::Null),
                })))
        });

        let block_expr = block
            .or(if_);

        let block_chain = block_expr.clone().then(block_expr.clone().repeated())
            .foldl(|a, b| Expr::Then(Box::new(a), Box::new(b)));

        block_chain.or(raw_expr.clone())
            .then(just(Token::Ctrl(';')).padding_for(expr.or_not()).repeated())
            .foldl(|a, b| Expr::Then(Box::new(a), Box::new(match b {
                Some(b) => b,
                None => Expr::Value(Value::Null),
            })))
    })
}

fn funcs_parser() -> impl Parser<Token, HashMap<String, Func>, Error = Simple<Token>> + Clone {
    let ident = filter_map(|span, tok| match tok {
        Token::Ident(ident) => Ok(ident.clone()),
        _ => Err(Simple::expected_token_found(Some(span), Vec::new(), Some(tok))),
    });

    let args = ident.clone()
        .chain(just(Token::Ctrl(',')).padding_for(ident.clone()).repeated())
        .padded_by(just(Token::Ctrl(',')).or_not())
        .or_not()
        .map(|items| items.unwrap_or_else(Vec::new));

    let func = just(Token::Fn)
        .padding_for(ident.label("function name"))
        .then(args
            .delimited_by(Token::Ctrl('('), Token::Ctrl(')'))
            .map(|expr| expr.unwrap_or_else(Vec::new)))
        .then(expr_parser()
            .delimited_by(Token::Ctrl('{'), Token::Ctrl('}'))
            .map(|expr| expr.unwrap_or(Expr::Error)))
        .map(|((name, args), body)| (name, Func {
            args,
            body,
        }));

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

    match lexer().parse(src.as_str()) {
        Ok(tokens) => {
            println!("Tokens = {:?}", tokens);
            match funcs_parser().parse(tokens) {
                Ok(funcs) => {
                    println!("{:#?}", funcs);
                    if let Some(main) = funcs.get("main") {
                        assert_eq!(main.args.len(), 0);
                        println!("Return value: {}", eval_expr(&main.body, &funcs, &mut Vec::new()));
                    } else {
                        panic!("No main function!");
                    }
                },
                Err(errs) => errs
                    .into_iter()
                    .for_each(|e| println!("Error: {:?}", e)),
            }
        },
        Err(errs) => errs
            .into_iter()
            .for_each(|e| println!("Error: {}", e)),
    }
}
