use chumsky::prelude::*;
use chumsky::pratt::*;

#[derive(Clone, Debug)]
pub enum Expr {
    Add(Box<Self>, Box<Self>),
    Sub(Box<Self>, Box<Self>),
    Mul(Box<Self>, Box<Self>),
    Div(Box<Self>, Box<Self>),
    Pow(Box<Self>, Box<Self>),
    Neg(Box<Self>),
    Factorial(Box<Self>),
    Deref(Box<Self>),
    Literal(i32),
}

#[derive(Clone, Debug)]
pub enum Stmt {
    Expr(Expr),
    Loop(Vec<Stmt>),
}

fn parser() -> impl Parser<'static, &'static str, Vec<Stmt>> {
    let atom = text::int(10)
        .from_str()
        .unwrapped()
        .map(Expr::Literal)
        .padded();

    let op = |c| just(c).padded();

    let expr = atom.pratt((
        postfix(5, op('!'), |lhs, _, _| Expr::Factorial(Box::new(lhs))),
        infix(right(4), op('^'), |l, _, r, _| Expr::Pow(Box::new(l), Box::new(r))),
        prefix(3, op('-'), |_, rhs, _| Expr::Neg(Box::new(rhs))),
        prefix(3, op('*'), |_, rhs, _| Expr::Deref(Box::new(rhs))),
        infix(left(1), op('+'), |l, _, r, _| Expr::Add(Box::new(l), Box::new(r))),
        infix(left(1), op('-'), |l, _, r, _| Expr::Sub(Box::new(l), Box::new(r))),
        infix(left(2), op('*'), |l, _, r, _| Expr::Mul(Box::new(l), Box::new(r))),
        infix(left(2), op('/'), |l, _, r, _| Expr::Div(Box::new(l), Box::new(r))),
    ));

    let block = recursive(|block| {
        let indent = just(' ')
            .repeated()
            .configure(|cfg, parent_indent| cfg.exactly(*parent_indent));


        let expr_stmt = expr
            .then_ignore(text::newline().or_not())
            .map(Stmt::Expr);

        let control_flow = just("loop:")
            .then(text::newline())
            .ignore_then(block)
            .map(Stmt::Loop);

        let stmt = control_flow.or(expr_stmt);

        text::whitespace()
            .count()
            .ignore_with_ctx(stmt.separated_by(indent).collect())
    });

    block.with_ctx(0)
}

fn main() {
    let stmts = parser().padded().parse(
        r#"

loop:
  *1 + -2 * 3!
  loop:
        10
        
"#,
    );
    println!("Parsed statements:\n{:?}", stmts.output().unwrap());
    println!("Errors:\n{:?}", stmts.errors().collect::<Vec<_>>());
}
