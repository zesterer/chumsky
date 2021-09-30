use super::*;

pub struct Stream<'a, I, S: Span, Iter: Iterator<Item = (S, I)> + ?Sized = dyn Iterator<Item = (S, I)> + 'a> {
    pub(crate) phantom: PhantomData<&'a ()>,
    pub(crate) ctx: S::Context,
    pub(crate) offset: usize,
    pub(crate) buffer: Vec<Option<(S, I)>>,
    pub(crate) iter: Iter,
}

impl<'a, I: Clone, S: Span> Stream<'a, I, S> {
    pub(crate) fn offset(&self) -> usize { self.offset }

    fn pull_until(&mut self, offset: usize) -> &Option<(S, I)> {
        while self.buffer.len() <= offset {
            self.buffer.push(self.iter.next());
        }
        &self.buffer[offset]
    }

    pub(crate) fn next(&mut self) -> (usize, S, Option<I>) {
        match self.pull_until(self.offset).clone() {
            Some((span, out)) => {
                self.offset += 1;
                (self.offset, span, Some(out))
            },
            None => (self.offset, S::new(self.ctx.clone(), None..None), None),
        }
    }

    pub(crate) fn zero_span(&mut self) -> S {
        let start = self.pull_until(self.offset.saturating_sub(1)).as_ref().and_then(|(s, _)| s.end());
        let end = self.pull_until(self.offset).as_ref().and_then(|(s, _)| s.start());
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

impl<'a> From<&'a str> for Stream<'a, char, Range<Option<usize>>, Box<dyn Iterator<Item = (Range<Option<usize>>, char)> + 'a>> {
    fn from(s: &'a str) -> Self {
        Stream {
            phantom: PhantomData,
            ctx: (),
            offset: 0,
            buffer: Vec::new(),
            iter: Box::new(s.chars().enumerate().map(|(i, c)| (Some(i)..Some(i + 1), c))),
        }
    }
}
