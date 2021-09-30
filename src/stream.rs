use super::*;

pub struct Stream<'a, I, S: Span, Iter: Iterator<Item = (I, S)> + ?Sized = dyn Iterator<Item = (I, S)> + 'a> {
    pub(crate) phantom: PhantomData<&'a ()>,
    pub(crate) ctx: S::Context,
    pub(crate) eoi: S::Offset,
    pub(crate) offset: usize,
    pub(crate) buffer: Vec<Option<(I, S)>>,
    pub(crate) iter: Iter,
}

impl<'a, I, S: Span, Iter: Iterator<Item = (I, S)>> Stream<'a, I, S, Iter> {
    /// Create a new stream from an iterator of `(Token, Span)` tuples. Additionally, the input context (usually a file
    /// reference) and the end of input symbol must be provided.
    pub fn from_iter(ctx: S::Context, eoi: S::Offset, iter: Iter) -> Self {
        Self {
            phantom: PhantomData,
            ctx,
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

    fn pull_until(&mut self, offset: usize) -> &Option<(I, S)> {
        while self.buffer.len() <= offset {
            self.buffer.push(self.iter.next());
        }
        &self.buffer[offset]
    }

    pub(crate) fn next(&mut self) -> (usize, S, Option<I>) {
        match self.pull_until(self.offset).clone() {
            Some((out, span)) => {
                self.offset += 1;
                (self.offset - 1, span, Some(out))
            },
            None => (self.offset, S::new(self.ctx.clone(), self.eoi.clone()..self.eoi.clone()), None),
        }
    }

    pub(crate) fn zero_span(&mut self) -> S {
        let start = self.pull_until(self.offset.saturating_sub(1))
            .as_ref()
            .map(|(_, s)| s.end())
            .unwrap_or_else(|| self.eoi.clone());
        let end = self.pull_until(self.offset)
            .as_ref()
            .map(|(_, s)| s.start())
            .unwrap_or_else(|| self.eoi.clone());
        S::new(self.ctx.clone(), start..end)
    }

    pub(crate) fn attempt<R, F: FnOnce(&mut Self) -> (bool, R)>(&mut self, f: F) -> R {
        let old_offset = self.offset;
        let (commit, out) = f(self);
        if !commit {
            self.offset = old_offset;
        }
        out
    }

    pub(crate) fn try_parse<O, E, F: FnOnce(&mut Self) -> PResult<O, E>>(&mut self, f: F) -> PResult<O, E> {
        self.attempt(move |stream| {
            let out = f(stream);
            (out.1.is_ok(), out)
        })
    }
}

impl<'a> From<&'a str> for Stream<'a, char, Range<usize>, Box<dyn Iterator<Item = (char, Range<usize>)> + 'a>> {
    fn from(s: &'a str) -> Self {
        Self::from_iter((), s.chars().count(), Box::new(s.chars().enumerate().map(|(i, c)| (c, i..i + 1))))
    }
}

impl<'a, T: Clone> From<&'a [T]> for Stream<'a, T, Range<usize>, Box<dyn Iterator<Item = (T, Range<usize>)> + 'a>> {
    fn from(s: &'a [T]) -> Self {
        Self::from_iter((), s.len(), Box::new(s.iter().cloned().enumerate().map(|(i, x)| (x, i..i + 1))))
    }
}

impl<'a, T: Clone, S: Clone + Span<Context = ()>> From<&'a [(T, S)]> for Stream<'a, T, S, Box<dyn Iterator<Item = (T, S)> + 'a>>
    where S::Offset: Default
{
    fn from(s: &'a [(T, S)]) -> Self {
        Self::from_iter((), Default::default(), Box::new(s.iter().cloned()))
    }
}
