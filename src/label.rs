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
        let old_alt = inp.errors.alt.take();
        let before = inp.offset();
        let res = self.parser.go::<M>(inp);

        // TODO: Label secondary errors too?
        let new_alt = inp.errors.alt.take();
        inp.errors.alt = old_alt;

        if let Some(mut new_alt) = new_alt {
            if new_alt.pos == before.offset.into() + 1 {
                new_alt.err.label_with(self.label.clone());
            }
            inp.add_alt_err(new_alt.pos, new_alt.err);
        }

        res
    }

    go_extra!(O);
}
