use super::*;

pub trait Span {
    type Context;
    type Offset;
}

impl<T> Span for Range<T> {
    type Context = ();
    type Offset = T;
}

impl<Ctx, S: Span> Span for (Ctx, S) {
    type Context = Ctx;
    type Offset = S::Offset;
}
