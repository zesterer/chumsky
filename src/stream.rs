use super::*;

pub struct Stream<'a, I, Iter: ?Sized = dyn Iterator<Item = I> + 'a> {
    pub(crate) phantom: PhantomData<&'a ()>,
    pub(crate) offset: usize,
    pub(crate) buffer: Vec<Option<I>>,
    pub(crate) iter: Iter,
}

impl<'a, I: Clone> Stream<'a, I> {
    pub(crate) fn offset(&self) -> usize { self.offset }

    pub(crate) fn next(&mut self) -> (usize, Option<I>) {
        if self.buffer.len() <= self.offset {
            self.buffer.push(self.iter.next());
        }

        let out = (self.offset, self.buffer[self.offset].clone());
        if out.1.is_some() {
            self.offset += 1;
        }
        out
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

impl<'a> From<&'a str> for Stream<'a, char, std::str::Chars<'a>> {
    fn from(s: &'a str) -> Self {
        Stream {
            phantom: PhantomData,
            offset: 0,
            buffer: Vec::new(),
            iter: s.chars(),
        }
    }
}
