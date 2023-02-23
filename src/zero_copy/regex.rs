//! Implementations of regex-based parsers

use super::*;

/// See [`regex`].
pub struct Regex<C: Char, I: ?Sized, E> {
    regex: C::Regex,
    phantom: PhantomData<(E, I)>,
}

/// Match input based on a provided regex pattern
pub fn regex<C: Char, I: ?Sized, E>(pattern: &str) -> Regex<C, I, E> {
    Regex {
        regex: C::new_regex(pattern),
        phantom: PhantomData,
    }
}

impl<'a, C, I, E> Parser<'a, I, &'a C::Str, E> for Regex<C, I, E>
where
    C: Char,
    I: StrInput<'a, C>,
    E: ParserExtra<'a, I>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, &'a C::Str, E::Error> {
        let before = inp.offset();
        C::match_regex(&self.regex, inp.slice_trailing())
            .map(|len| {
                let before = inp.offset();
                inp.skip_bytes(len);
                let after = inp.offset();
                M::bind(|| inp.slice(before..after))
            })
            // TODO: Make this error actually correct
            .ok_or_else(|| {
                Located::at(
                    inp.offset().into(),
                    E::Error::expected_found(None, None, inp.span_since(before)),
                )
            })
    }

    go_extra!(&'a C::Str);
}
