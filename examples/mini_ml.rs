//! This is an entire lexer, parser, type-checker, and interpreter for a statically-typed ML-like functional
//! programming language. See `sample.mini_ml` for sample source code.
//! Run it with the following command:
//! cargo run --features=pratt,label --example mini_ml -- examples/sample.mini_ml

use ariadne::{sources, Color, Label, Report, ReportKind};
use chumsky::{
    input::{Input as _, MappedInput},
    pratt::*,
    prelude::*,
};
use std::{env, fmt, fs};

// Tokens and lexer

#[derive(Debug, Clone, PartialEq)]
pub enum Token<'src> {
    Ident(&'src str),
    Num(f64),
    Parens(Vec<Spanned<Self>>),

    // Ops
    Eq,
    Plus,
    Asterisk,

    // Keywords
    Let,
    In,
    Fn,
    True,
    False,
}

impl fmt::Display for Token<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Token::Ident(x) => write!(f, "{x}"),
            Token::Num(x) => write!(f, "{x}"),
            Token::Parens(_) => write!(f, "(...)"),
            Token::Eq => write!(f, "="),
            Token::Plus => write!(f, "+"),
            Token::Asterisk => write!(f, "*"),
            Token::Let => write!(f, "let"),
            Token::In => write!(f, "in"),
            Token::Fn => write!(f, "fn"),
            Token::True => write!(f, "true"),
            Token::False => write!(f, "false"),
        }
    }
}

fn lexer<'src>(
) -> impl Parser<'src, &'src str, Vec<Spanned<Token<'src>>>, extra::Err<Rich<'src, char>>> {
    recursive(|token| {
        choice((
            // Keywords
            text::ident().map(|s| match s {
                "let" => Token::Let,
                "in" => Token::In,
                "fn" => Token::Fn,
                "true" => Token::True,
                "false" => Token::False,
                s => Token::Ident(s),
            }),
            // Operators
            just("=").to(Token::Eq),
            just("+").to(Token::Plus),
            just("*").to(Token::Asterisk),
            // Numbers
            text::int(10)
                .then(just('.').then(text::digits(10)).or_not())
                .to_slice()
                .map(|s: &str| Token::Num(s.parse().unwrap())),
            token
                .repeated()
                .collect()
                .delimited_by(just('('), just(')'))
                .labelled("token tree")
                .as_context()
                .map(Token::Parens),
        ))
        .spanned()
        .padded()
    })
    .repeated()
    .collect()
}

// AST and parser

#[derive(Clone, Debug)]
pub enum Expr<'src> {
    Var(&'src str),
    Num(f64),
    Bool(bool),
    Add(Box<Spanned<Self>>, Box<Spanned<Self>>),
    Mul(Box<Spanned<Self>>, Box<Spanned<Self>>),
    Let {
        lhs: Spanned<&'src str>,
        rhs: Box<Spanned<Self>>,
        then: Box<Spanned<Self>>,
    },
    Apply {
        func: Box<Spanned<Self>>,
        arg: Box<Spanned<Self>>,
    },
    Func {
        arg: Box<Spanned<&'src str>>,
        body: Box<Spanned<Self>>,
    },
}

fn parser<'tokens, 'src: 'tokens>() -> impl Parser<
    'tokens,
    MappedInput<'tokens, Token<'src>, SimpleSpan, &'tokens [Spanned<Token<'src>>]>,
    Spanned<Expr<'src>>,
    extra::Err<Rich<'tokens, Token<'src>>>,
> {
    recursive(|expr| {
        let ident = select_ref! { Token::Ident(x) => *x };
        let atom = choice((
            select_ref! { Token::Num(x) => Expr::Num(*x) },
            just(Token::True).to(Expr::Bool(true)),
            just(Token::False).to(Expr::Bool(false)),
            ident.map(Expr::Var),
            // let x = y in z
            just(Token::Let)
                .ignore_then(ident.spanned())
                .then_ignore(just(Token::Eq))
                .then(expr.clone())
                .then_ignore(just(Token::In))
                .then(expr.clone())
                .map(|((lhs, rhs), then)| Expr::Let {
                    lhs,
                    rhs: Box::new(rhs),
                    then: Box::new(then),
                }),
        ));

        choice((
            atom.spanned(),
            // fn x y = z
            just(Token::Fn).ignore_then(ident.spanned().repeated().foldr_with(
                just(Token::Eq).ignore_then(expr.clone()),
                |arg, body, e| {
                    Expr::Func {
                        arg: Box::new(arg),
                        body: Box::new(body),
                    }
                    .with_span(e.span())
                },
            )),
            // ( x )
            expr.nested_in(select_ref! { Token::Parens(ts) = e => ts.split_spanned(e.span()) }),
        ))
        .pratt(vec![
            // Multiply
            infix(left(10), just(Token::Asterisk), |x, _, y, e| {
                Expr::Mul(Box::new(x), Box::new(y)).with_span(e.span())
            })
            .boxed(),
            // Add
            infix(left(9), just(Token::Plus), |x, _, y, e| {
                Expr::Add(Box::new(x), Box::new(y)).with_span(e.span())
            })
            .boxed(),
            // Calls
            infix(left(1), empty(), |x, _, y, e| {
                Expr::Apply {
                    func: Box::new(x),
                    arg: Box::new(y),
                }
                .with_span(e.span())
            })
            .boxed(),
        ])
        .labelled("expression")
        .as_context()
    })
}

// Type checker/solver

#[derive(Copy, Clone, Debug, PartialEq)]
struct TyVar(usize);

#[derive(Copy, Clone, Debug)]
enum TyInfo {
    Unknown,
    Ref(TyVar),
    Num,
    Bool,
    Func(TyVar, TyVar),
}

impl fmt::Display for TyInfo {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TyInfo::Unknown => write!(f, "?"),
            TyInfo::Ref(_) => write!(f, "<ref>"),
            TyInfo::Num => write!(f, "Num"),
            TyInfo::Bool => write!(f, "Bool"),
            TyInfo::Func(_, _) => write!(f, "(_ -> _)"),
        }
    }
}

#[derive(Debug)]
enum Ty {
    Num,
    Bool,
    Func(Box<Self>, Box<Self>),
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Ty::Num => write!(f, "Num"),
            Ty::Bool => write!(f, "Bool"),
            Ty::Func(x, y) => write!(f, "{x} -> {y}"),
        }
    }
}

struct Solver<'src> {
    src: &'src str,
    vars: Vec<(TyInfo, SimpleSpan)>,
}

impl Solver<'_> {
    fn create_ty(&mut self, info: TyInfo, span: SimpleSpan) -> TyVar {
        self.vars.push((info, span));
        TyVar(self.vars.len() - 1)
    }

    fn unify(&mut self, a: TyVar, b: TyVar, span: SimpleSpan) {
        match (self.vars[a.0].0, self.vars[b.0].0) {
            (TyInfo::Unknown, _) => self.vars[a.0].0 = TyInfo::Ref(b),
            (_, TyInfo::Unknown) => self.vars[b.0].0 = TyInfo::Ref(a),
            (TyInfo::Ref(a), _) => self.unify(a, b, span),
            (_, TyInfo::Ref(b)) => self.unify(a, b, span),
            (TyInfo::Num, TyInfo::Num) | (TyInfo::Bool, TyInfo::Bool) => {}
            (TyInfo::Func(a_i, a_o), TyInfo::Func(b_i, b_o)) => {
                self.unify(b_i, a_i, span); // Order swapped: function args are contravariant
                self.unify(a_o, b_o, span);
            }
            (a_info, b_info) => failure(
                format!("Type mismatch between {a_info} and {b_info}"),
                ("mismatch occurred here".to_string(), span),
                vec![
                    (format!("{a_info}"), self.vars[a.0].1),
                    (format!("{b_info}"), self.vars[b.0].1),
                ],
                self.src,
            ),
        }
    }

    fn check<'src>(
        &mut self,
        expr: &Spanned<Expr<'src>>,
        env: &mut Vec<(&'src str, TyVar)>,
    ) -> TyVar {
        match &**expr {
            Expr::Num(_) => self.create_ty(TyInfo::Num, expr.span),
            Expr::Bool(_) => self.create_ty(TyInfo::Bool, expr.span),
            Expr::Var(name) => {
                env.iter()
                    .rev()
                    .find(|(n, _)| n == name)
                    .unwrap_or_else(|| {
                        failure(
                            format!("No such local '{name}'"),
                            ("not found in scope".to_string(), expr.span),
                            None,
                            self.src,
                        )
                    })
                    .1
            }
            Expr::Let { lhs, rhs, then } => {
                let rhs_ty = self.check(rhs, env);
                env.push((**lhs, rhs_ty));
                let out_ty = self.check(then, env);
                env.pop();
                out_ty
            }
            Expr::Func { arg, body } => {
                let arg_ty = self.create_ty(TyInfo::Unknown, arg.span);
                env.push((&**arg, arg_ty));
                let body_ty = self.check(body, env);
                env.pop();
                self.create_ty(TyInfo::Func(arg_ty, body_ty), expr.span)
            }
            Expr::Apply { func, arg } => {
                let func_ty = self.check(func, env);
                let arg_ty = self.check(arg, env);
                let out_ty = self.create_ty(TyInfo::Unknown, expr.span);
                let func_req_ty = self.create_ty(TyInfo::Func(arg_ty, out_ty), func.span);
                self.unify(func_req_ty, func_ty, expr.span);
                out_ty
            }
            Expr::Add(l, r) | Expr::Mul(l, r) => {
                let out_ty = self.create_ty(TyInfo::Num, expr.span);
                let l_ty = self.check(l, env);
                self.unify(out_ty, l_ty, expr.span);
                let r_ty = self.check(r, env);
                self.unify(out_ty, r_ty, expr.span);
                out_ty
            }
        }
    }

    pub fn solve(&self, var: TyVar) -> Ty {
        match self.vars[var.0].0 {
            TyInfo::Unknown => failure(
                "Cannot infer type".to_string(),
                ("has unknown type".to_string(), self.vars[var.0].1),
                None,
                self.src,
            ),
            TyInfo::Ref(var) => self.solve(var),
            TyInfo::Num => Ty::Num,
            TyInfo::Bool => Ty::Bool,
            TyInfo::Func(i, o) => Ty::Func(Box::new(self.solve(i)), Box::new(self.solve(o))),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Value<'src> {
    Num(f64),
    Bool(bool),
    Func {
        arg: Spanned<&'src str>,
        env: Scope<'src>,
        body: &'src Spanned<Expr<'src>>,
    },
}

impl Value<'_> {
    pub fn num(self) -> f64 {
        let Value::Num(x) = self else { panic!() };
        x
    }
}

type Scope<'src> = Vec<(Spanned<&'src str>, Value<'src>)>;

#[derive(Default)]
pub struct Vm<'src> {
    stack: Scope<'src>,
}

impl<'src> Vm<'src> {
    pub fn eval(&mut self, expr: &'src Spanned<Expr<'src>>) -> Value<'src> {
        match &**expr {
            Expr::Num(x) => Value::Num(*x),
            Expr::Bool(x) => Value::Bool(*x),
            Expr::Var(var) => self
                .stack
                .iter()
                .rev()
                .find(|(v, _)| **v == *var)
                .unwrap()
                .1
                .clone(),
            Expr::Let { lhs, rhs, then } => {
                let rhs = self.eval(rhs);
                self.stack.push((*lhs, rhs));
                let then = self.eval(then);
                self.stack.pop();
                then
            }
            Expr::Func { arg, body } => Value::Func {
                arg: **arg,
                env: self.stack.clone(), // TODO: Only save what's actually needed by the function body
                body,
            },
            Expr::Apply { func, arg } => {
                let func = self.eval(func);
                let arg_val = self.eval(arg);
                let Value::Func { arg, body, mut env } = func else {
                    panic!()
                };
                let old_len = self.stack.len();
                self.stack.append(&mut env);
                self.stack.push((arg, arg_val));
                let out = self.eval(body);
                self.stack.truncate(old_len);
                out
            }
            Expr::Add(x, y) => Value::Num(self.eval(x).num() + self.eval(y).num()),
            Expr::Mul(x, y) => Value::Num(self.eval(x).num() * self.eval(y).num()),
        }
    }
}

fn failure(
    msg: String,
    label: (String, SimpleSpan),
    extra_labels: impl IntoIterator<Item = (String, SimpleSpan)>,
    src: &str,
) -> ! {
    let fname = "example";
    Report::build(ReportKind::Error, (fname, label.1.into_range()))
        .with_config(ariadne::Config::new().with_index_type(ariadne::IndexType::Byte))
        .with_message(&msg)
        .with_label(
            Label::new((fname, label.1.into_range()))
                .with_message(label.0)
                .with_color(Color::Red),
        )
        .with_labels(extra_labels.into_iter().map(|label2| {
            Label::new((fname, label2.1.into_range()))
                .with_message(label2.0)
                .with_color(Color::Yellow)
        }))
        .finish()
        .print(sources([(fname, src)]))
        .unwrap();
    std::process::exit(1)
}

fn parse_failure(err: &Rich<impl fmt::Display>, src: &str) -> ! {
    failure(
        err.reason().to_string(),
        (
            err.found()
                .map(|c| c.to_string())
                .unwrap_or_else(|| "end of input".to_string()),
            *err.span(),
        ),
        err.contexts()
            .map(|(l, s)| (format!("while parsing this {l}"), *s)),
        src,
    )
}

fn main() {
    let filename = env::args().nth(1).expect("Expected file argument");
    let src = &fs::read_to_string(&filename).expect("Failed to read file");

    let tokens = lexer()
        .parse(src)
        .into_result()
        .unwrap_or_else(|errs| parse_failure(&errs[0], src));

    let expr = parser()
        .parse(tokens[..].split_spanned((0..src.len()).into()))
        .into_result()
        .unwrap_or_else(|errs| parse_failure(&errs[0], src));

    let mut solver = Solver {
        src,
        vars: Vec::new(),
    };
    let program_ty = solver.check(&expr, &mut Vec::new());
    println!("Result type: {:?}", solver.solve(program_ty));

    let mut vm = Vm::default();
    println!("Result: {:?}", vm.eval(&expr));
}
