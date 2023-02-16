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

impl<'a, C, I, E> Parser<'a, I, &'a C::Slice, E> for Regex<C, I, E>
where
    C: Char,
    C::Slice: 'a,
    I: Input + StrInput<C> + ?Sized,
    E: ParserExtra<'a, I>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, &'a C::Slice, E::Error> {
        let before = inp.save();
        C::match_regex(&self.regex, inp.slice_trailing())
            .map(|len| {
                let before = inp.save();
                inp.skip_bytes(len);
                let after = inp.save();
                M::bind(|| inp.slice(before..after))
            })
            // TODO: Make this error actually correct
            .ok_or_else(|| {
                Located::at(
                    inp.save(),
                    E::Error::expected_found(None, None, inp.span_since(before)),
                )
            })
    }

    go_extra!(&'a C::Slice);
}
