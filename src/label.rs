//! Items related to parser labelling.

use super::*;

/// A trait implemented by [`Error`]s that can originate from labelled parsers. See [`Parser::labelled`].
pub trait LabelError<'src, I: Input<'src>, L>: Sized {
    /// Create a new error describing a conflict between expected inputs and that which was actually found.
    ///
    /// `found` having the value `None` indicates that the end of input was reached, but was not expected.
    ///
    /// An expected input having the value `None` indicates that the end of input was expected.
    fn expected_found<E: IntoIterator<Item = L>>(
        expected: E,
        found: Option<MaybeRef<'src, I::Token>>,
        span: I::Span,
    ) -> Self;

    /// Fast path for `a.merge(LabelError::expected_found(...))` that may incur less overhead by, for example, reusing allocations.
    #[inline(always)]
    fn merge_expected_found<E: IntoIterator<Item = L>>(
        self,
        expected: E,
        found: Option<MaybeRef<'src, I::Token>>,
        span: I::Span,
    ) -> Self
    where
        Self: Error<'src, I>,
    {
        self.merge(LabelError::expected_found(expected, found, span))
    }

    /// Fast path for `a = LabelError::expected_found(...)` that may incur less overhead by, for example, reusing allocations.
    #[inline(always)]
    fn replace_expected_found<E: IntoIterator<Item = L>>(
        self,
        expected: E,
        found: Option<MaybeRef<'src, I::Token>>,
        span: I::Span,
    ) -> Self {
        LabelError::expected_found(expected, found, span)
    }

    /// Annotate the expected patterns within this parser with the given label.
    ///
    /// In practice, this usually removes all other labels and expected tokens in favor of a single label that
    /// represents the overall pattern.
    fn label_with(&mut self, label: L) {
        #![allow(unused_variables)]
    }

    /// Annotate this error, indicating that it occurred within the context denoted by the given label.
    ///
    /// A span that runs from the beginning of the context up until the error location is also provided.
    ///
    /// In practice, this usually means adding the context to a context 'stack', similar to a backtrace.
    fn in_context(&mut self, label: L, span: I::Span) {
        #![allow(unused_variables)]
    }
}

/// See [`Parser::labelled`].
#[derive(Copy, Clone)]
pub struct Labelled<A, L> {
    pub(crate) parser: A,
    pub(crate) label: L,
    pub(crate) is_context: bool,
    pub(crate) is_builtin: bool,
}

impl<A, L> Labelled<A, L> {
    /// Specify that the label should be used as context when reporting errors.
    ///
    /// This allows error messages to use this label to add information to errors that occur *within* this parser.
    pub fn as_context(self) -> Self {
        Self {
            is_context: true,
            ..self
        }
    }

    pub(crate) fn as_builtin(mut self) -> Self {
        self.is_builtin = true;
        self
    }
}

impl<'src, I, O, E, A, L> Parser<'src, I, O, E> for Labelled<A, L>
where
    I: Input<'src>,
    E: ParserExtra<'src, I>,
    A: Parser<'src, I, O, E>,
    L: Clone,
    E::Error: LabelError<'src, I, L>,
{
    #[doc(hidden)]
    #[cfg(feature = "debug")]
    fn node_info(&self, scope: &mut debug::NodeScope) -> debug::NodeInfo {
        (&self.parser)
            .labelled_with(|| self.label.clone())
            .node_info(scope)
    }

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'src, '_, I, E>) -> PResult<M, O> {
        LabelledWith {
            is_context: self.is_context,
            is_builtin: self.is_builtin,
            ..(&self.parser).labelled_with(|| self.label.clone())
        }
        .go::<M>(inp)
    }

    go_extra!(O);
}

/// See [`Parser::labelled_with`].
pub struct LabelledWith<A, L, F> {
    pub(crate) parser: A,
    pub(crate) label: F,
    pub(crate) is_context: bool,
    pub(crate) is_builtin: bool,
    pub(crate) phantom: PhantomData<L>,
}

impl<A, L, F> Clone for LabelledWith<A, L, F>
where
    A: Clone,
    F: Clone,
{
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            label: self.label.clone(),
            is_context: self.is_context,
            is_builtin: self.is_builtin,
            phantom: PhantomData,
        }
    }
}

impl<A, L, F> Copy for LabelledWith<A, L, F>
where
    A: Copy,
    F: Copy,
{
}

impl<A, L, F> LabelledWith<A, L, F> {
    /// Specify that the label should be used as context when reporting errors.
    ///
    /// This allows error messages to use this label to add information to errors that occur *within* this parser.
    pub fn as_context(self) -> Self {
        Self {
            is_context: true,
            ..self
        }
    }

    pub(crate) fn as_builtin(mut self) -> Self {
        self.is_builtin = true;
        self
    }
}

impl<'src, I, O, E, A, L, F> Parser<'src, I, O, E> for LabelledWith<A, L, F>
where
    I: Input<'src>,
    E: ParserExtra<'src, I>,
    A: Parser<'src, I, O, E>,
    F: Fn() -> L,
    E::Error: LabelError<'src, I, L>,
{
    #[doc(hidden)]
    #[cfg(feature = "debug")]
    fn node_info(&self, scope: &mut debug::NodeScope) -> debug::NodeInfo {
        trait LabelString {
            fn label_string(&self) -> String;
        }
        impl<T> LabelString for T {
            default fn label_string(&self) -> String {
                core::any::type_name::<Self>().to_string()
            }
        }
        impl<T: core::fmt::Debug> LabelString for T {
            default fn label_string(&self) -> String {
                format!("{self:?}")
            }
        }
        impl<T: core::fmt::Debug> LabelString for TextExpected<T> {
            fn label_string(&self) -> String {
                match self {
                    Self::AnyIdentifier => format!("identifier"),
                    Self::Identifier(s) => format!("{s:?}"),
                    Self::Digit(start, end) => format!(
                        "digit{}{}",
                        if *start == 0 {
                            format!("")
                        } else {
                            format!(", >= {start}")
                        },
                        if *end == 10 {
                            format!("")
                        } else {
                            format!(", base {end}")
                        },
                    ),
                    _ => format!("{self:?}"),
                }
            }
        }

        let label_string = (self.label)().label_string();

        if self.is_builtin {
            debug::NodeInfo::Builtin(label_string)
        } else {
            debug::NodeInfo::Labelled(label_string, Box::new(self.parser.node_info(scope)))
        }
    }

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'src, '_, I, E>) -> PResult<M, O> {
        let old_alt = inp.errors.alt.take();
        let before = inp.save();
        let res = self.parser.go::<M>(inp);

        // TODO: Label secondary errors too?
        let new_alt = inp.errors.alt.take();
        inp.errors.alt = old_alt;

        if let Some(mut new_alt) = new_alt {
            let before_loc = I::cursor_location(&before.cursor().inner);
            let new_alt_loc = I::cursor_location(&new_alt.pos);
            if new_alt_loc == before_loc {
                new_alt.err.label_with((self.label)());
            } else if self.is_context && new_alt_loc > before_loc {
                // SAFETY: cursors generated by previous call to `InputRef::next` (or similar).
                let span = unsafe { I::span(inp.cache, &before.cursor().inner..&new_alt.pos) };
                new_alt.err.in_context((self.label)(), span);
            }
            inp.add_alt_err(&new_alt.pos, new_alt.err);
        }

        if self.is_context {
            for i in before.err_count..inp.errors.secondary.len() {
                let label = (self.label)();
                let err = &mut inp.errors.secondary[i];
                // SAFETY: cursors generated by previous call to `InputRef::next` (or similar).
                let span = unsafe { I::span(inp.cache, &before.cursor().inner..&err.pos) };
                err.err.in_context(label, span);
            }
        }

        res
    }

    go_extra!(O);
}
