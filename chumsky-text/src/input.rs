use chumsky::{
    input::{SliceInput, ValueInput, WithContext},
    span::Span,
};

use crate::char::Char;

// Implemented by inputs that reference a string slice and use byte indices as their offset.
/// A trait for types that represent string-like streams of input tokens
pub trait StrInput<'a, C: Char>:
    ValueInput<'a, Offset = usize, Token = C> + SliceInput<'a, Slice = &'a C::Str>
{
}

impl<'a, Ctx, C, I> StrInput<'a, C> for WithContext<Ctx, I>
where
    I: StrInput<'a, C>,
    I::Span: Span<Context = ()>,
    Ctx: Clone + 'a,
    C: Char,
{
}

impl<'a> StrInput<'a, char> for &'a str {}

impl<'a> StrInput<'a, u8> for &'a [u8] {}

impl<'a, const N: usize> StrInput<'a, u8> for &'a [u8; N] {}
