use ariadne::{Color, Label, Report, ReportKind, Source};
use chumsky::{combinator::Repeated, extra::Full, prelude::*, text::ident};

#[derive(Debug, Clone, Copy, Default)]
enum IndentCtx {
    /// We're at the root level and haven't begun parsing the root block.
    #[default]
    Root,
    /// We're parsing a block whose leading indent is exactly that many long.
    Block(usize),
    /// We're in a context in which all whitespace is fair game, including newlines. Don't worry about indentation.
    ///
    /// We came from a context with this much indentation, in case we need to re-activate it.
    ///
    /// Not implemented for this example; just here to show what's possible.
    #[allow(unused)]
    Disabled(usize),
}

type Extras<'a> = Full<Rich<'a, char>, (), IndentCtx>;

/// Can't use [`chumsky::text::whitespace`] as we don't want to allow newlines here unless we're in `IndentCtx::Disabled`
fn ws<'a>() -> Repeated<impl Parser<'a, &'a str, (), Extras<'a>> + Copy, (), &'a str, Extras<'a>> {
    let space = just(' ').labelled("space");
    let nl = just('\n').labelled("newline");
    choice((
        space,
        // Though not implemented for this example, this is where e.g. newlines could be allowed inside `(...)`.
        nl.contextual()
            .configure(|_, ctx| matches!(ctx, IndentCtx::Disabled(_))),
    ))
    .ignored()
    .repeated()
    .at_least(0)
}

/// Parse the same indent of this block, or nothing at all if we're at the root level and haven't started parsing the
/// root block yet.
///
/// Used to separate lines of a block *after* a newline has been parsed for that line.
fn samedent<'a>() -> impl Parser<'a, &'a str, (), Extras<'a>> + Copy {
    let empty_lines = just(' ')
        .repeated()
        .at_least(0)
        .then(just('\n'))
        .repeated()
        .at_least(0);
    empty_lines
        .ignore_then(ws().count())
        .try_map_with(|n, ext| match *ext.ctx() {
            IndentCtx::Root if n != 0 => {
                Err(Rich::custom(ext.span(), "No indent allowed at root level"))
            }
            IndentCtx::Root => Ok(()),
            IndentCtx::Block(pdent) if n > pdent => {
                Err(Rich::custom(ext.span(), format!("Unexpected indent from {pdent} to {n}")))
            }
            IndentCtx::Block(pdent) if n < pdent => {
                Err(Rich::custom(ext.span(), format!("Unexpected dedent from {pdent} to {n}")))
            }
            IndentCtx::Block(_) /* n == pdent */ => Ok(()),
            IndentCtx::Disabled(_) => todo!(),
        })
}

/// Parse a new indent (i.e. greater indent than our parent, if any.) and return what the new ctx should be.
///
/// Only used at the beginning of a block.
fn indent<'a>() -> impl Parser<'a, &'a str, IndentCtx, Extras<'a>> + Copy {
    let empty_lines = just(' ')
        .repeated()
        .at_least(0)
        .then(just('\n'))
        .repeated()
        .at_least(0);
    empty_lines
        .ignore_then(ws().count())
        .try_map_with(|n, ext| match *ext.ctx() {
            IndentCtx::Root if n != 0 => {
                Err(Rich::custom(ext.span(), "No indent allowed at root level"))
            }
            IndentCtx::Root => Ok(IndentCtx::Block(0)),
            IndentCtx::Block(pdent) if n > pdent => Ok(IndentCtx::Block(n)),
            IndentCtx::Block(pdent) if n < pdent => {
                Err(Rich::custom(ext.span(), format!("Unexpected dedent from {pdent} to {n}")))
            }
            IndentCtx::Block(pdent) /* n == pdent */ => {
                Err(Rich::custom(ext.span(), format!("Expected indent beyond {pdent}")))
            },
            IndentCtx::Disabled(_) => Err(Rich::custom(
                ext.span(),
                "Refusing to match a block in a non-indent zone",
            )),
        })
}

#[derive(Clone, Debug)]
pub enum Stmt {
    Expr,
    Loop(Vec<Stmt>),
}

fn parser<'a>() -> impl Parser<'a, &'a str, Vec<Stmt>, Extras<'a>> {
    let expr = ident(); // TODO

    let block = recursive(|block| {
        let expr_stmt = expr.then_ignore(text::newline()).to(Stmt::Expr);
        let control_flow = just("loop:")
            .then(text::newline())
            .ignore_then(block)
            .map(Stmt::Loop);
        let stmt = expr_stmt.or(control_flow);

        // Matched at the beginning of the block to determine what indent the block should use:
        indent()
            // ignore_with_ctx sets the value that indent later uses:
            .ignore_with_ctx(stmt.separated_by(samedent()).collect())
    });

    block.with_ctx(IndentCtx::Root)
}

fn show_result(input: &str) {
    let (res, errs) = parser().parse(input).into_output_errors();
    println!("Final parse result: {res:#?}");
    errs.into_iter().for_each(|e| {
        Report::build(ReportKind::Error, ((), e.span().into_range()))
            .with_config(ariadne::Config::new().with_index_type(ariadne::IndexType::Byte))
            .with_message(e.to_string())
            .with_label(
                Label::new(((), e.span().into_range()))
                    .with_message(e.reason().to_string())
                    .with_color(Color::Red),
            )
            .finish()
            .print(Source::from(&input))
            .unwrap()
    });
}

fn main() {
    eprintln!("Well-formed example:");
    show_result(
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

    eprintln!("Example with bad indent:");
    show_result(
        r#"
foo
bar
loop:
    baz
    loop:
    caz
    car
    dar
daz
"#,
    );
}
