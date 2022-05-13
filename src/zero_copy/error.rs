use super::*;

pub trait Error<I: Input + ?Sized> {
    fn expected_found<E: IntoIterator<Item = Option<I::Token>>>(
        expected: E,
        found: Option<I::Token>,
        span: I::Span,
    ) -> Self;
}

impl<I: Input> Error<I> for () {
    fn expected_found<E: IntoIterator<Item = Option<I::Token>>>(
        expected: E,
        found: Option<I::Token>,
        span: I::Span,
    ) -> Self {}
}
