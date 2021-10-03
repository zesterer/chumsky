use super::*;

/// A helper trait for [`Stream`]. There is no need to implement this trait yourself, nor do you need to care about its
/// existence. It is marked as 'deprecated' to discourage its use and to indicate that it is not part of the crate's
/// semver guarantees.
#[deprecated(note = "This trait is excluded from the semver guarantees of chumsky. If you decide to use it, broken builds are your fault.")]
pub trait StreamExtend<T>: Iterator<Item = T> {
    /// Extend the vector with input. The actual amount can be more or less than `n`.
    fn extend(&mut self, v: &mut Vec<T>, n: usize);
}

#[allow(deprecated)]
impl<I: Iterator> StreamExtend<I::Item> for I {
    fn extend(&mut self, v: &mut Vec<I::Item>, n: usize) {
        v.reserve(n);
        v.extend(self.take(n));
    }
}

/// A type that represents a stream of input tokens. Unlike [`Iterator`], this type supports backtracking and a few
/// other features required by the crate.
#[allow(deprecated)]
pub struct Stream<'a, I, S: Span, Iter: Iterator<Item = (I, S)> + ?Sized = dyn StreamExtend<(I, S)> + 'a> {
    pub(crate) phantom: PhantomData<&'a ()>,
    pub(crate) eoi: S,
    pub(crate) offset: usize,
    pub(crate) buffer: Vec<(I, S)>,
    pub(crate) iter: Iter,
}

impl<'a, I, S: Span, Iter: Iterator<Item = (I, S)>> Stream<'a, I, S, Iter> {
    /// Create a new stream from an iterator of `(Token, Span)` tuples. A span representing the end of input must also
    /// be provided.
    ///
    /// There is no requirement that spans must map exactly to the position of inputs in the stream, but they should
    /// be non-overlapping and should appear in a monotonically-increasing order.
    pub fn from_iter(eoi: S, iter: Iter) -> Self {
        Self {
            phantom: PhantomData,
            eoi,
            offset: 0,
            buffer: Vec::new(),
            iter,
        }
    }
}

impl<'a, I: Clone, S: Span> Stream<'a, I, S> {
    pub(crate) fn offset(&self) -> usize { self.offset }

    pub(crate) fn save(&self) -> usize { self.offset }
    pub(crate) fn revert(&mut self, offset: usize) { self.offset = offset; }

    fn pull_until(&mut self, offset: usize) -> Option<&(I, S)> {
        let additional = offset.saturating_sub(self.buffer.len()) + 1024;
        #[allow(deprecated)]
        self.iter.extend(&mut self.buffer, additional);
        self.buffer.get(offset)
    }

    pub(crate) fn next(&mut self) -> (usize, S, Option<I>) {
        match self.pull_until(self.offset).cloned() {
            Some((out, span)) => {
                self.offset += 1;
                (self.offset - 1, span, Some(out))
            },
            None => (self.offset, self.eoi.clone(), None),
        }
    }

    pub(crate) fn span_since(&mut self, start: usize) -> S {
        let start = self.pull_until(start)
            .as_ref()
            .map(|(_, s)| s.start())
            .unwrap_or_else(|| self.eoi.start());
        let end = self.pull_until(self.offset.saturating_sub(1))
            .as_ref()
            .map(|(_, s)| s.end())
            .unwrap_or_else(|| self.eoi.end());
        S::new(self.eoi.context(), start..end)
    }

    pub(crate) fn attempt<R, F: FnOnce(&mut Self) -> (bool, R)>(&mut self, f: F) -> R {
        let old_offset = self.offset;
        let (commit, out) = f(self);
        if !commit {
            self.offset = old_offset;
        }
        out
    }

    pub(crate) fn try_parse<O, E, F: FnOnce(&mut Self) -> PResult<I, O, E>>(&mut self, f: F) -> PResult<I, O, E> {
        self.attempt(move |stream| {
            let out = f(stream);
            (out.1.is_ok(), out)
        })
    }
}

impl<'a> From<&'a str> for Stream<'a, char, Range<usize>, Box<dyn Iterator<Item = (char, Range<usize>)> + 'a>> {
    fn from(s: &'a str) -> Self {
        let len = s.chars().count();
        Self::from_iter(len..len + 1, Box::new(s.chars().enumerate().map(|(i, c)| (c, i..i + 1))))
    }
}

impl<'a, T: Clone> From<&'a [T]> for Stream<'a, T, Range<usize>, Box<dyn Iterator<Item = (T, Range<usize>)> + 'a>> {
    fn from(s: &'a [T]) -> Self {
        let len = s.len();
        Self::from_iter(len..len + 1, Box::new(s.iter().cloned().enumerate().map(|(i, x)| (x, i..i + 1))))
    }
}

impl<'a, T: Clone + 'a, const N: usize> From<[T; N]> for Stream<'a, T, Range<usize>, Box<dyn Iterator<Item = (T, Range<usize>)> + 'a>> {
    fn from(s: [T; N]) -> Self {
        let len = s.len();
        Self::from_iter(len..len + 1, Box::new(std::array::IntoIter::new(s).enumerate().map(|(i, x)| (x, i..i + 1))))
    }
}

// impl<'a, T: Clone, S: Clone + Span<Context = ()>> From<&'a [(T, S)]> for Stream<'a, T, S, Box<dyn Iterator<Item = (T, S)> + 'a>>
//     where S::Offset: Default
// {
//     fn from(s: &'a [(T, S)]) -> Self {
//         Self::from_iter(Default::default(), Box::new(s.iter().cloned()))
//     }
// }
