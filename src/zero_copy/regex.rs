use super::*;

pub struct Regex<C: Char, I: ?Sized, E = (), S = ()> {
    regex: C::Regex,
    phantom: PhantomData<(E, S, I)>,
}

pub fn regex<C: Char, I: ?Sized, E, S>(pattern: &str) -> Regex<C, I, E, S> {
    Regex {
        regex: C::new_regex(pattern),
        phantom: PhantomData,
    }
}

impl<'a, C, I, E, S> Parser<'a, I, E, S> for Regex<C, I, E, S>
where
    C: Char,
    C::Slice: 'a,
    I: Input + StrInput<C> + ?Sized,
    E: Error<I>,
    S: 'a,
{
    type Output = &'a C::Slice;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E> {
        let before = inp.save();
        C::match_regex(&self.regex, inp.slice_trailing())
            .map(|len| {
                let before = inp.save();
                inp.skip_bytes(len);
                let after = inp.save();
                M::bind(|| inp.slice(before..after))
            })
            // TODO: Make this error actually correct
            .ok_or_else(|| Located::at(inp.last_pos(), E::expected_found(None, None, inp.span_since(before))))
    }

    go_extra!();
}
