use ariadne::{Color, Label, Report, ReportKind, Source};
use chumsky::{extra::Full, prelude::*, text};

type Extras<'a> = Full<Rich<'a, char>, (), &'a str>;

/// Parse any amount of indentation at the start of a line, ignoring preding empty lines
fn indent<'a>() -> impl Parser<'a, &'a str, &'a str, Extras<'a>> + Copy {
    let empty_lines = text::inline_whitespace().then(text::newline()).repeated();
    empty_lines.ignore_then(text::inline_whitespace().to_slice())
}

#[derive(Clone, Debug)]
pub enum Stmt {
    Expr,
    Loop(Vec<Stmt>),
}

fn parser<'a>() -> impl Parser<'a, &'a str, Vec<Stmt>, Extras<'a>> {
    let expr = text::ident(); // TODO

    // Parses everything beyond the initial indentation in a block
    let block = recursive(|block| {
        let block_start_indent = indent().try_map_with(move |indent, ext| match *ext.ctx() {
            ctx if indent.starts_with(ctx) && indent.len() > ctx.len() => Ok(indent),
            ctx => Err(Rich::custom(
                ext.span(),
                format!("Indent must increase here"),
            )),
        });

        let expr_stmt = expr.then_ignore(text::newline()).to(Stmt::Expr);
        let control_flow = just("loop:")
            .then(text::newline())
            // First, we parse some indentation to determine what indentation the new block should have
            .ignore_then(block_start_indent.ignore_with_ctx(block))
            .map(Stmt::Loop);
        let stmt = expr_stmt.or(control_flow);

        let block_continue_indent = indent().try_map_with(move |indent, ext| match *ext.ctx() {
            ctx if indent == ctx => Ok(indent),
            ctx if ctx.starts_with(indent) => {
                Err(Rich::custom(ext.span(), format!("Unexpected deindent")))
            }
            ctx if indent.starts_with(ctx) => {
                Err(Rich::custom(ext.span(), format!("Unexpected indent")))
            }
            ctx => Err(Rich::custom(
                ext.span(),
                format!("Mismatched indent: expected {ctx:?}, found {indent:?}"),
            )),
        });

        stmt.separated_by(block_continue_indent).collect()
    });

    // The root block always has no indentation
    indent()
        .try_map_with(|indent, ext| {
            if indent != "" {
                Err(Rich::custom(ext.span(), "No indent allowed at root level"))
            } else {
                Ok("")
            }
        })
        .ignore_with_ctx(block)
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
