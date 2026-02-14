use chumsky::prelude::*;

#[derive(Clone, Debug)]
pub enum Stmt {
    Expr,
    Loop(Vec<Stmt>),
}

fn parser<'a>() -> impl Parser<'a, &'a str, Vec<Stmt>> {
    let expr = just("expr"); // TODO

    let block = recursive(|block| {
        // Matched between each statement of the block:
        let indent = just(' ')
            .repeated()
            // The initial whitespace sets it unconditionally, so unwrapping here is safe.
            .configure(|cfg, parent_indent: &Option<usize>| cfg.exactly(parent_indent.unwrap()));

        let expr_stmt = expr.then_ignore(text::newline()).to(Stmt::Expr);
        let control_flow = just("loop:")
            .then(text::newline())
            .ignore_then(block)
            .map(Stmt::Loop);
        let stmt = expr_stmt.or(control_flow);

        // Matched at the beginning of the block to determine what indent the block should use:
        text::whitespace()
            // If we skipped `.configure(...)`, then it would count any level of indent as being
            // our block, allowing it to parse something like:
            //
            // loop:
            //   loop:
            // expr
            // loop:
            //   expr
            //
            // as loop(loop(expr, loop(expr))) instead of (rightly) being an error.
            .configure(|cfg, parent_indent| {
                if let Some(p) = parent_indent {
                    // Non-root statements must be greater than their parents.
                    cfg.at_least(p + 1)
                } else {
                    // Root-level statements must be un-indented.
                    cfg.exactly(0)
                }
            })
            .count()
            .map(Some)
            // ignore_with_ctx sets the value that indent later uses:
            .ignore_with_ctx(stmt.separated_by(indent).collect())
    });

    block.with_ctx(None)
}

fn main() {
    eprintln!("Well-formed example:");
    let stmts = parser().padded().parse(
        r#"
expr
expr
loop:
    expr
    loop:
        expr
        expr
    expr
expr
"#,
    );
    println!("{:#?}", stmts.output());
    println!("{:?}", stmts.errors().collect::<Vec<_>>());

    eprintln!("Example with bad indent:");
    let stmts = parser().padded().parse(
        r#"
expr
expr
loop:
    expr
    loop:
    expr
    expr
    expr
expr
"#,
    );
    println!("{:#?}", stmts.output());
    println!("{:?}", stmts.errors().collect::<Vec<_>>());
}
