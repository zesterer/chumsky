use super::*;

pub trait Error<I: Input + ?Sized>: Sized {
    fn expected_found<E: IntoIterator<Item = Option<I::Token>>>(
        expected: E,
        found: Option<I::Token>,
        span: I::Span,
    ) -> Self;

    fn merge(self, other: Self) -> Self {
        #![allow(unused_variables)]
        self
    }
}

impl<I: Input + ?Sized> Error<I> for () {
    fn expected_found<E: IntoIterator<Item = Option<I::Token>>>(
        _: E,
        _: Option<I::Token>,
        _: I::Span,
    ) -> Self {
    }
}

pub struct Simple<I: Input + ?Sized> {
    span: I::Span,
    found: Option<I::Token>,
}

impl<I: Input + ?Sized> Error<I> for Simple<I> {
    fn expected_found<E: IntoIterator<Item = Option<I::Token>>>(
        _expected: E,
        found: Option<I::Token>,
        span: I::Span,
    ) -> Self {
        Self { span, found }
    }
}

impl<I: Input + ?Sized> fmt::Debug for Simple<I>
where
    I::Span: fmt::Debug,
    I::Token: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "found ")?;
        write_token_debug(f, &self.found)?;
        write!(f, " at {:?}", self.span)?;
        Ok(())
    }
}

pub struct Rich<I: Input + ?Sized> {
    span: I::Span,
    expected: Vec<Option<I::Token>>,
    found: Option<I::Token>,
}

impl<I: Input + ?Sized> Error<I> for Rich<I>
where
    I::Token: PartialEq,
{
    fn expected_found<E: IntoIterator<Item = Option<I::Token>>>(
        expected: E,
        found: Option<I::Token>,
        span: I::Span,
    ) -> Self {
        Self {
            span,
            expected: expected.into_iter().collect(),
            found,
        }
    }

    fn merge(mut self, other: Self) -> Self {
        for expected in other.expected {
            if !self.expected.contains(&expected) {
                self.expected.push(expected);
            }
        }
        self
    }
}

impl<I: Input + ?Sized> fmt::Debug for Rich<I>
where
    I::Span: fmt::Debug,
    I::Token: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "found ")?;
        write_token_debug(f, &self.found)?;
        write!(f, " at {:?}, expected ", self.span)?;
        match &self.expected[..] {
            [] => write!(f, "something else")?,
            [expected] => write_token_debug(f, expected)?,
            _ => {
                write!(f, "one of ")?;
                for expected in &self.expected[..self.expected.len() - 1] {
                    write_token_debug(f, expected)?;
                    write!(f, ", ")?;
                }
                write!(f, "or ")?;
                write_token_debug(f, self.expected.last().unwrap())?;
            }
        }
        Ok(())
    }
}

fn write_token_debug<T: fmt::Debug>(f: &mut fmt::Formatter, tok: &Option<T>) -> fmt::Result {
    match tok {
        Some(tok) => write!(f, "{:?}", tok),
        None => write!(f, "end of input"),
    }
}
