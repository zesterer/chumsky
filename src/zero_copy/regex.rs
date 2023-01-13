use super::*;

<<<<<<< HEAD
pub struct Regex<C: Char, I: ?Sized, E = EmptyErr, S = ()> {
=======
pub struct Regex<C: Char, In: ?Sized, E = (), S = ()> {
>>>>>>> The great rename, add ctx
    regex: C::Regex,
    phantom: PhantomData<(E, S, I)>,
}

pub fn regex<C: Char, In: ?Sized, Err, State>(pattern: &str) -> Regex<C, In, Err, State> {
    Regex {
        regex: C::new_regex(pattern),
        phantom: PhantomData,
    }
}

impl<'a, C, In, Err, State> Parser<'a, I, &'a C::Slice, Err, State> for Regex<C, In, Err, State>
where
    C: Char,
    C::Slice: 'a,
    In: Input + StrInput<C> + ?Sized,
    Err: Error<In>,
    State: 'a,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, &'a C::Slice, Err> {
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
                    inp.last_pos(),
                    Err::expected_found(None, None, inp.span_since(before)),
                )
            })
    }

    go_extra!(&'a C::Slice);
}
