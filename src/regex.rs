use super::{*, text::Character};

pub struct Regex<C: Character>(C::Regex);

impl<C: Character> Parser<C, C::Collection> for Regex<C> {
    type Error = ();

    fn parse_inner<D: Debugger>(&self, _debugger: &mut D, stream: &mut StreamOf<I, E>) -> PResult<I, O, E> {
        (self.0)(stream)
    }

    fn parse_inner_verbose(&self, d: &mut Verbose, s: &mut StreamOf<I, E>) -> PResult<I, O, E> { #[allow(deprecated)] self.parse_inner(d, s) }
    fn parse_inner_silent(&self, d: &mut Silent, s: &mut StreamOf<I, E>) -> PResult<I, O, E> { #[allow(deprecated)] self.parse_inner(d, s) }
}
