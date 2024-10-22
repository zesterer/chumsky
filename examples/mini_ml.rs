use chumsky::{input::SpannedInput, pratt::*, prelude::*};

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

pub type Spanned<T> = (T, SimpleSpan);

fn lexer<'src>(
) -> impl Parser<'src, &'src str, Vec<Spanned<Token<'src>>>, extra::Err<Rich<'src, char>>> {
    recursive(|token| {
        let keyword = text::ident().map(|s| match s {
            "let" => Token::Let,
            "in" => Token::In,
            "fn" => Token::Fn,
            "true" => Token::True,
            "false" => Token::False,
            s => Token::Ident(s),
        });

        let num = text::int(10)
            .then(just('.').then(text::digits(10)).or_not())
            .to_slice()
            .map(|s: &str| Token::Num(s.parse().unwrap()));

        let op = choice((
            just("=").to(Token::Eq),
            just("+").to(Token::Plus),
            just("*").to(Token::Asterisk),
        ));

        choice((
            keyword,
            op,
            num,
            token
                .repeated()
                .collect()
                .delimited_by(just('(').padded(), just(')').padded())
                .map(Token::Parens),
        ))
        .map_with(|t, e| (t, e.span()))
        .padded()
    })
    .repeated()
    .collect()
}

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

type ParserInput<'src> = SpannedInput<Token<'src>, SimpleSpan, &'src [Spanned<Token<'src>>]>;

fn parser<'src>(
) -> impl Parser<'src, ParserInput<'src>, Spanned<Expr<'src>>, extra::Err<Rich<'src, Token<'src>>>>
{
    recursive(|expr| {
        let ident = select_ref! { Token::Ident(x) => *x };
        let atom = choice((
            select_ref! { Token::Num(x) => Expr::Num(*x) },
            just(Token::True).to(Expr::Bool(true)),
            just(Token::False).to(Expr::Bool(false)),
            ident.map(Expr::Var),
            // let x = y in z
            just(Token::Let)
                .ignore_then(ident.map_with(|x, e| (x, e.span())))
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
            atom.map_with(|expr, e| (expr, e.span())),
            // fn x y = z
            just(Token::Fn).ignore_then(
                ident.map_with(|x, e| (x, e.span())).repeated().foldr_with(
                    just(Token::Eq).ignore_then(expr.clone()),
                    |arg, body, e| {
                        (
                            Expr::Func {
                                arg: Box::new(arg),
                                body: Box::new(body),
                            },
                            e.span(),
                        )
                    },
                ),
            ),
            // ( x )
            expr.nested_in(
                select_ref! { Token::Parens(ts) = e => ts.as_slice().spanned(e.span()) },
            ),
        ))
        .pratt((
            // Multiply
            infix(left(10), just(Token::Asterisk), |x, _, y, e| {
                (Expr::Mul(Box::new(x), Box::new(y)), e.span())
            }),
            // Add
            infix(left(9), just(Token::Plus), |x, _, y, e| {
                (Expr::Add(Box::new(x), Box::new(y)), e.span())
            }),
            // Calls
            infix(left(1), empty(), |x, _, y, e| {
                (
                    Expr::Apply {
                        func: Box::new(x),
                        arg: Box::new(y),
                    },
                    e.span(),
                )
            }),
        ))
    })
}

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

#[derive(Debug)]
enum Ty {
    Num,
    Bool,
    Func(Box<Self>, Box<Self>),
}

#[derive(Default)]
struct Solver {
    vars: Vec<TyInfo>,
}

impl Solver {
    fn create_ty(&mut self, info: TyInfo) -> TyVar {
        self.vars.push(info);
        TyVar(self.vars.len() - 1)
    }

    fn unify(&mut self, a: TyVar, b: TyVar) {
        match (self.vars[a.0], self.vars[b.0]) {
            (TyInfo::Unknown, _) => self.vars[a.0] = TyInfo::Ref(b),
            (_, TyInfo::Unknown) => self.vars[b.0] = TyInfo::Ref(a),
            (TyInfo::Ref(a), _) => self.unify(a, b),
            (_, TyInfo::Ref(b)) => self.unify(a, b),
            (TyInfo::Num, TyInfo::Num) | (TyInfo::Bool, TyInfo::Bool) => {}
            (TyInfo::Func(a_i, a_o), TyInfo::Func(b_i, b_o)) => {
                self.unify(a_i, b_i);
                self.unify(a_o, b_o);
            }
            (a, b) => panic!("Type mismatch between {a:?} and {b:?}"),
        }
    }

    fn check<'ast>(&mut self, expr: &Expr<'ast>, env: &mut Vec<(&'ast str, TyVar)>) -> TyVar {
        match expr {
            // Literal expressions are easy, their type doesn't need inferring.
            Expr::Num(_) => self.create_ty(TyInfo::Num),
            Expr::Bool(_) => self.create_ty(TyInfo::Bool),
            // We search the environment backward until we find a binding matching the variable name.
            Expr::Var(name) => {
                env.iter_mut()
                    .rev()
                    .find(|(n, _)| n == name)
                    .expect("No such variable in scope")
                    .1
            }
            // In a let expression, `rhs` gets bound with name `lhs` in the environment used to type-check `then`.
            Expr::Let { lhs, rhs, then } => {
                let rhs = self.check(&rhs.0, env);
                env.push((lhs.0, rhs));
                let out = self.check(&then.0, env);
                env.pop();
                out
            }
            // In a function, the argument becomes an unknown type in the environment used to type-check `body`.
            Expr::Func { arg, body } => {
                let arg_ty = self.create_ty(TyInfo::Unknown);
                env.push((arg.0, arg_ty));
                let body = self.check(&body.0, env);
                env.pop();
                self.create_ty(TyInfo::Func(arg_ty, body))
            }
            // During function application, both argument and function are type-checked and then we force the latter to be a function of the former.
            Expr::Apply { func, arg } => {
                let func = self.check(&func.0, env);
                let arg = self.check(&arg.0, env);
                let out = self.create_ty(TyInfo::Unknown);
                let func_ty = self.create_ty(TyInfo::Func(arg, out));
                self.unify(func_ty, func);
                out
            }
            Expr::Add(l, r) | Expr::Mul(l, r) => {
                let out = self.create_ty(TyInfo::Num);
                let l = self.check(&l.0, env);
                self.unify(out, l);
                let r = self.check(&r.0, env);
                self.unify(out, r);
                out
            }
        }
    }

    pub fn solve(&self, var: TyVar) -> Ty {
        match self.vars[var.0] {
            TyInfo::Unknown => panic!("Cannot infer type"),
            TyInfo::Ref(var) => self.solve(var),
            TyInfo::Num => Ty::Num,
            TyInfo::Bool => Ty::Bool,
            TyInfo::Func(i, o) => Ty::Func(Box::new(self.solve(i)), Box::new(self.solve(o))),
        }
    }
}

fn main() {
    let text = "
        let add = fn x y = x + y in
        let mul = fn x y = x * y in
        let x = mul (add 5 42) 2 in
        add x 3.5
    ";

    let tokens = lexer().parse(text).unwrap();

    dbg!(&tokens);

    let expr = parser()
        .parse(tokens.spanned((0..text.len()).into()))
        .unwrap();

    dbg!(&expr);

    let mut solver = Solver::default();

    let program_ty = solver.check(&expr.0, &mut Vec::new());

    println!(
        "The expression outputs type `{:?}`",
        solver.solve(program_ty)
    );
}
