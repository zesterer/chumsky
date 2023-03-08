//! Items related to parser labelling.

use super::*;

/// A trait implemented by [`Error`]s that can orginate from labelled parsers. See [`Parser::labelled`].
pub trait LabelError<'a, I: Input<'a>, L>: Error<'a, I> {
    /// Label this parser with the given label.
    ///
    /// In practice, this usually removes all other labels and expected tokens in favour of a single label.
    fn label_with(&mut self, label: L);
}

/// See [`Parser::labelled`].
#[derive(Copy, Clone)]
pub struct Labelled<A, L> {
    pub(crate) parser: A,
    pub(crate) label: L,
}

impl<'a, I, O, E, A, L> ParserSealed<'a, I, O, E> for Labelled<A, L>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, O, E>,
    L: Clone,
    E::Error: LabelError<'a, I, L>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        let before = inp.offset();
        let res = self.parser.go::<M>(inp);

        // TODO: Label secondary errors too?
        if res.is_err() {
            let err = inp.errors.alt.as_mut().expect("error but no alt?");
            if err.pos == before.into() + 1 {
                err.err.label_with(self.label.clone());
            }
        }

        res
    }

    go_extra!(O);
}
