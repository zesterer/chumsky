use chumsky::{
    input::{MapExtra, SpannedInput},
    pratt::*,
    prelude::*,
};

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
}

pub type Spanned<T> = (T, SimpleSpan);

fn lexer<'src>(
) -> impl Parser<'src, &'src str, Vec<Spanned<Token<'src>>>, extra::Err<Rich<'src, char>>> {
    recursive(|token| {
        let keyword = text::ident().map(|s| match s {
            "let" => Token::Let,
            "in" => Token::In,
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

#[derive(Debug)]
pub enum Expr<'src> {
    Local(&'src str),
    Num(f64),
    Let(&'src str, Box<Spanned<Self>>, Box<Spanned<Self>>),
    Add(Box<Spanned<Self>>, Box<Spanned<Self>>),
    Mul(Box<Spanned<Self>>, Box<Spanned<Self>>),
    Call(Box<Spanned<Self>>, Box<Spanned<Self>>),
}

type ParserInput<'src> = SpannedInput<Token<'src>, SimpleSpan, &'src [Spanned<Token<'src>>]>;

fn parser<'src>(
) -> impl Parser<'src, ParserInput<'src>, Spanned<Expr<'src>>, extra::Err<Rich<'src, Token<'src>>>>
{
    recursive(|expr| {
        let ident = select_ref! { Token::Ident(x) => *x };
        let atom = choice((
            select_ref! { Token::Num(x) => Expr::Num(*x) },
            ident.map(Expr::Local),
            // let x = y in z
            just(Token::Let)
                .ignore_then(ident)
                .then_ignore(just(Token::Eq))
                .then(expr.clone())
                .then_ignore(just(Token::In))
                .then(expr.clone())
                .map(|((lhs, rhs), then)| Expr::Let(lhs, Box::new(rhs), Box::new(then))),
        ));

        atom.map_with(|expr, e| (expr, e.span()))
            // ( x )
            .or(expr.nested_in(
                select_ref! { Token::Parens(ts) = e => ts.as_slice().spanned(e.span()) },
            ))
            .pratt((
                // Multiply
                infix(
                    left(10),
                    just(Token::Asterisk),
                    |x, _, y, e: &mut MapExtra<'src, '_, _, _>| {
                        (Expr::Mul(Box::new(x), Box::new(y)), e.span())
                    },
                ),
                // Add
                infix(
                    left(9),
                    just(Token::Plus),
                    |x, _, y, e: &mut MapExtra<'src, '_, _, _>| {
                        (Expr::Add(Box::new(x), Box::new(y)), e.span())
                    },
                ),
                // Calls
                infix(
                    left(1),
                    empty(),
                    |x, _, y, e: &mut MapExtra<'src, '_, _, _>| {
                        (Expr::Call(Box::new(x), Box::new(y)), e.span())
                    },
                ),
            ))
    })
}

fn main() {
    let text = "
        let x = (5 + 42) * 2 in
        add x 3.5
    ";

    let tokens = lexer().parse(text).unwrap();

    dbg!(&tokens);

    let expr = parser().parse(tokens.spanned((0..text.len()).into()));

    dbg!(expr);
}
