use super::*;
use core::mem::MaybeUninit;
use hashbrown::HashSet;

pub struct MapSlice<A, F, E = (), S = ()> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
    pub(crate) phantom: PhantomData<(E, S)>,
}

impl<A: Copy, F: Copy, E, S> Copy for MapSlice<A, F, E, S> {}
impl<A: Clone, F: Clone, E, S> Clone for MapSlice<A, F, E, S> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            mapper: self.mapper.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, S, A, F, O> Parser<'a, I, E, S> for MapSlice<A, F, E, S>
where
    I: Input + SliceInput + ?Sized,
    E: Error<I>,
    S: 'a,
    I::Slice: 'a,
    A: Parser<'a, I, E, S>,
    F: Fn(&'a I::Slice) -> O,
{
    type Output = O;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E> {
        let before = inp.save();
        self.parser.go::<Check>(inp)?;
        let after = inp.save();

        Ok(M::bind(|| (self.mapper)(inp.slice(before..after))))
    }

    go_extra!();
}

pub struct Filter<A, F> {
    pub(crate) parser: A,
    pub(crate) filter: F,
}

impl<A: Copy + ?Sized, F: Copy> Copy for Filter<A, F> {}
impl<A: Clone, F: Clone> Clone for Filter<A, F> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            filter: self.filter.clone(),
        }
    }
}

impl<'a, A, I, E, S, F> Parser<'a, I, E, S> for Filter<A, F>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, E, S>,
    F: Fn(&A::Output) -> bool,
{
    type Output = A::Output;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E> {
        let before = inp.save();
        self.parser.go::<Emit>(inp).and_then(|out| {
            if (self.filter)(&out) {
                Ok(M::bind(|| out))
            } else {
                let span = inp.span_since(before);
                Err(Located::at(
                    inp.last_pos(),
                    E::expected_found(None, None, span),
                ))
            }
        })
    }

    go_extra!();
}

#[derive(Copy, Clone)]
pub struct Map<A, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
}

impl<'a, I, E, S, A, F, O> Parser<'a, I, E, S> for Map<A, F>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, E, S>,
    F: Fn(A::Output) -> O,
{
    type Output = O;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E> {
        self.parser
            .go::<M>(inp)
            .map(|out| M::map(out, &self.mapper))
    }

    go_extra!();
}

#[derive(Copy, Clone)]
pub struct MapWithSpan<A, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
}

impl<'a, I, E, S, A, F, O> Parser<'a, I, E, S> for MapWithSpan<A, F>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, E, S>,
    F: Fn(A::Output, I::Span) -> O,
{
    type Output = O;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E> {
        let before = inp.save();
        self.parser.go::<M>(inp).map(|out| {
            M::map(out, |out| {
                let span = inp.span_since(before);
                (self.mapper)(out, span)
            })
        })
    }

    go_extra!();
}

#[derive(Copy, Clone)]
pub struct MapWithState<A, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
}

impl<'a, I, E, S, A, F, O> Parser<'a, I, E, S> for MapWithState<A, F>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, E, S>,
    F: Fn(A::Output, I::Span, &mut S) -> O,
{
    type Output = O;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E> {
        let before = inp.save();
        self.parser.go::<Emit>(inp).map(|out| {
            M::bind(|| {
                let span = inp.span_since(before);
                let state = inp.state();
                (self.mapper)(out, span, state)
            })
        })
    }

    go_extra!();
}

#[derive(Copy, Clone)]
pub struct TryMap<A, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
}

impl<'a, I, E, S, A, F, O> Parser<'a, I, E, S> for TryMap<A, F>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, E, S>,
    F: Fn(A::Output, I::Span) -> Result<O, E>,
{
    type Output = O;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E> {
        let before = inp.save();
        self.parser.go::<Emit>(inp).and_then(|out| {
            let span = inp.span_since(before);
            match (self.mapper)(out, span) {
                Ok(out) => Ok(M::bind(|| out)),
                Err(e) => Err(Located::at(inp.last_pos(), e)),
            }
        })
    }

    go_extra!();
}

#[derive(Copy, Clone)]
pub struct TryMapWithState<A, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
}

impl<'a, I, E, S, A, F, O> Parser<'a, I, E, S> for TryMapWithState<A, F>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, E, S>,
    F: Fn(A::Output, I::Span, &mut S) -> Result<O, E>,
{
    type Output = O;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E> {
        let before = inp.save();
        self.parser.go::<Emit>(inp).and_then(|out| {
            let span = inp.span_since(before);
            let state = inp.state();
            match (self.mapper)(out, span, state) {
                Ok(out) => Ok(M::bind(|| out)),
                Err(e) => Err(Located::at(inp.last_pos(), e)),
            }
        })
    }

    go_extra!();
}

pub struct To<A, O, E = (), S = ()> {
    pub(crate) parser: A,
    pub(crate) to: O,
    pub(crate) phantom: PhantomData<(E, S)>,
}

impl<A: Copy, O: Copy, E, S> Copy for To<A, O, E, S> {}
impl<A: Clone, O: Clone, E, S> Clone for To<A, O, E, S> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            to: self.to.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, S, A, O> Parser<'a, I, E, S> for To<A, O, E, S>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, E, S>,
    O: Clone,
{
    type Output = O;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E> {
        self.parser
            .go::<Check>(inp)
            .map(|_| M::bind(|| self.to.clone()))
    }

    go_extra!();
}

pub type Ignored<A, E = (), S = ()> = To<A, (), E, S>;

pub struct Then<A, B, E = (), S = ()> {
    pub(crate) parser_a: A,
    pub(crate) parser_b: B,
    pub(crate) phantom: PhantomData<(E, S)>,
}

impl<A: Copy, B: Copy, E, S> Copy for Then<A, B, E, S> {}
impl<A: Clone, B: Clone, E, S> Clone for Then<A, B, E, S> {
    fn clone(&self) -> Self {
        Self {
            parser_a: self.parser_a.clone(),
            parser_b: self.parser_b.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, S, A, B> Parser<'a, I, E, S> for Then<A, B, E, S>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, E, S>,
    B: Parser<'a, I, E, S>,
{
    type Output = (A::Output, B::Output);

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E> {
        let a = self.parser_a.go::<M>(inp)?;
        let b = self.parser_b.go::<M>(inp)?;
        Ok(M::combine(a, b, |a: A::Output, b: B::Output| (a, b)))
    }

    go_extra!();
}

pub struct IgnoreThen<A, B, E = (), S = ()> {
    pub(crate) parser_a: A,
    pub(crate) parser_b: B,
    pub(crate) phantom: PhantomData<(E, S)>,
}

impl<A: Copy, B: Copy, E, S> Copy for IgnoreThen<A, B, E, S> {}
impl<A: Clone, B: Clone, E, S> Clone for IgnoreThen<A, B, E, S> {
    fn clone(&self) -> Self {
        Self {
            parser_a: self.parser_a.clone(),
            parser_b: self.parser_b.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, S, A, B> Parser<'a, I, E, S> for IgnoreThen<A, B, E, S>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, E, S>,
    B: Parser<'a, I, E, S>,
{
    type Output = B::Output;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E> {
        let _a = self.parser_a.go::<Check>(inp)?;
        let b = self.parser_b.go::<M>(inp)?;
        Ok(M::map(b, |b: B::Output| b))
    }

    go_extra!();
}

pub struct ThenIgnore<A, B, E = (), S = ()> {
    pub(crate) parser_a: A,
    pub(crate) parser_b: B,
    pub(crate) phantom: PhantomData<(E, S)>,
}

impl<A: Copy, B: Copy, E, S> Copy for ThenIgnore<A, B, E, S> {}
impl<A: Clone, B: Clone, E, S> Clone for ThenIgnore<A, B, E, S> {
    fn clone(&self) -> Self {
        Self {
            parser_a: self.parser_a.clone(),
            parser_b: self.parser_b.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, S, A, B> Parser<'a, I, E, S> for ThenIgnore<A, B, E, S>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, E, S>,
    B: Parser<'a, I, E, S>,
{
    type Output = A::Output;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E> {
        let a = self.parser_a.go::<M>(inp)?;
        let _b = self.parser_b.go::<Check>(inp)?;
        Ok(M::map(a, |a: A::Output| a))
    }

    go_extra!();
}

pub struct ThenWith<A, B, F, I: ?Sized, E = (), S = ()> {
    pub(crate) parser: A,
    pub(crate) then: F,
    pub(crate) phantom: PhantomData<(B, E, S, I)>,
}

impl<A: Copy, B, F: Copy, I: ?Sized, E, S> Copy for ThenWith<A, B, F, I, E, S> {}
impl<A: Clone, B, F: Clone, I: ?Sized, E, S> Clone for ThenWith<A, B, F, I, E, S> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            then: self.then.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, S, A, B, F> Parser<'a, I, E, S> for ThenWith<A, B, F, I, E, S>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, E, S>,
    B: Parser<'a, I, E, S>,
    F: Fn(A::Output) -> B,
{
    type Output = B::Output;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E> {
        let before = inp.save();
        match self.parser.go::<Emit>(inp) {
            Ok(output) => {
                let then = (self.then)(output);

                let before = inp.save();
                match then.go::<M>(inp) {
                    Ok(output) => Ok(output),
                    Err(e) => {
                        inp.rewind(before);
                        Err(e)
                    }
                }
            }
            Err(e) => {
                inp.rewind(before);
                Err(e)
            }
        }
    }

    go_extra!();
}

#[derive(Copy, Clone)]
pub struct DelimitedBy<A, B, C> {
    pub(crate) parser: A,
    pub(crate) start: B,
    pub(crate) end: C,
}

impl<'a, I, E, S, A, B, C> Parser<'a, I, E, S> for DelimitedBy<A, B, C>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, E, S>,
    B: Parser<'a, I, E, S>,
    C: Parser<'a, I, E, S>,
{
    type Output = A::Output;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E> {
        let _ = self.start.go::<Check>(inp)?;
        let b = self.parser.go::<M>(inp)?;
        let _ = self.end.go::<Check>(inp)?;
        Ok(b)
    }

    go_extra!();
}

#[derive(Copy, Clone)]
pub struct PaddedBy<A, B> {
    pub(crate) parser: A,
    pub(crate) padding: B,
}

impl<'a, I, E, S, A, B> Parser<'a, I, E, S> for PaddedBy<A, B>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, E, S>,
    B: Parser<'a, I, E, S>,
{
    type Output = A::Output;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E> {
        let _ = self.padding.go::<Check>(inp)?;
        let b = self.parser.go::<M>(inp)?;
        let _ = self.padding.go::<Check>(inp)?;
        Ok(b)
    }

    go_extra!();
}

#[derive(Copy, Clone)]
pub struct Or<A, B> {
    pub(crate) parser_a: A,
    pub(crate) parser_b: B,
}

impl<'a, I, E, S, A, B> Parser<'a, I, E, S> for Or<A, B>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, E, S>,
    B: Parser<'a, I, E, S, Output = A::Output>,
{
    type Output = A::Output;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E> {
        let before = inp.save();
        match self.parser_a.go::<M>(inp) {
            Ok(out) => Ok(out),
            Err(ea) => {
                // TODO: prioritise errors
                inp.rewind(before);
                match self.parser_b.go::<M>(inp) {
                    Ok(out) => Ok(out),
                    Err(eb) => Err(ea.prioritize(eb, |a, b| a.merge(b))),
                }
            }
        }
    }

    go_extra!();
}

#[derive(Copy, Clone)]
pub struct RecoverWith<A, F> {
    pub(crate) parser: A,
    pub(crate) fallback: F,
}

impl<'a, I, E, S, A, F> Parser<'a, I, E, S> for RecoverWith<A, F>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, E, S>,
    F: Parser<'a, I, E, S, Output = A::Output>,
{
    type Output = A::Output;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E> {
        let before = inp.save();
        match self.parser.go::<M>(inp) {
            Ok(out) => Ok(out),
            Err(e) => {
                inp.rewind(before);
                match self.fallback.go::<M>(inp) {
                    Ok(out) => {
                        inp.emit(e.err);
                        Ok(out)
                    }
                    Err(_) => Err(e),
                }
            }
        }
    }

    go_extra!();
}

pub trait Container<T>: Default {
    fn push(&mut self, item: T);
}

impl<T> Container<T> for () {
    fn push(&mut self, _: T) {}
}

impl<T> Container<T> for Vec<T> {
    fn push(&mut self, item: T) {
        (*self).push(item);
    }
}

impl Container<char> for String {
    fn push(&mut self, item: char) {
        (*self).push(item)
    }
}

impl<K: Eq + Hash, V> Container<(K, V)> for HashMap<K, V> {
    fn push(&mut self, (key, value): (K, V)) {
        (*self).insert(key, value);
    }
}

#[cfg(feature = "std")]
impl<K: Eq + Hash, V> Container<(K, V)> for std::collections::HashMap<K, V> {
    fn push(&mut self, (key, value): (K, V)) {
        (*self).insert(key, value);
    }
}

impl<T: Eq + Hash> Container<T> for HashSet<T> {
    fn push(&mut self, item: T) {
        (*self).insert(item);
    }
}

#[cfg(feature = "std")]
impl<T: Eq + Hash> Container<T> for std::collections::HashSet<T> {
    fn push(&mut self, item: T) {
        (*self).insert(item);
    }
}

impl<K: Ord, V> Container<(K, V)> for alloc::collections::BTreeMap<K, V> {
    fn push(&mut self, (key, value): (K, V)) {
        (*self).insert(key, value);
    }
}

impl<T: Ord> Container<T> for alloc::collections::BTreeSet<T> {
    fn push(&mut self, item: T) {
        (*self).insert(item);
    }
}

pub struct Repeated<A, I: ?Sized, C = (), E = (), S = ()> {
    pub(crate) parser: A,
    pub(crate) at_least: usize,
    pub(crate) at_most: Option<usize>,
    pub(crate) phantom: PhantomData<(C, E, S, I)>,
}

impl<A: Copy, I: ?Sized, C, E, S> Copy for Repeated<A, I, C, E, S> {}
impl<A: Clone, I: ?Sized, C, E, S> Clone for Repeated<A, I, C, E, S> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            at_least: self.at_least,
            at_most: self.at_most,
            phantom: PhantomData,
        }
    }
}

impl<'a, A: Parser<'a, I, E, S>, I: Input + ?Sized, C, E: Error<I>, S: 'a> Repeated<A, I, C, E, S> {
    pub fn at_least(self, at_least: usize) -> Self {
        Self { at_least, ..self }
    }

    pub fn at_most(self, at_most: usize) -> Self {
        Self {
            at_most: Some(at_most),
            ..self
        }
    }

    pub fn exactly(self, exactly: usize) -> Self {
        Self {
            at_least: exactly,
            at_most: Some(exactly),
            ..self
        }
    }

    pub fn collect<D: Container<A::Output>>(self) -> Repeated<A, I, D, E, S>
    where
        A: Parser<'a, I, E, S>,
    {
        Repeated {
            parser: self.parser,
            at_least: self.at_least,
            at_most: self.at_most,
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, S, A, C> Parser<'a, I, E, S> for Repeated<A, I, C, E, S>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, E, S>,
    C: Container<A::Output>,
{
    type Output = C;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E> {
        let mut count = 0;
        let mut output = M::bind::<C, _>(|| C::default());
        loop {
            let before = inp.save();
            match self.parser.go::<M>(inp) {
                Ok(out) => {
                    output = M::map(output, |mut output: C| {
                        M::map(out, |out| output.push(out));
                        output
                    });
                    count += 1;

                    if let Some(at_most) = self.at_most {
                        if count >= at_most {
                            break Ok(output);
                        }
                    }
                }
                Err(e) => {
                    inp.rewind(before);
                    break if count >= self.at_least {
                        Ok(output)
                    } else {
                        Err(e)
                    };
                }
            }
        }
    }

    go_extra!();
}

pub struct SeparatedBy<A, B, I: ?Sized, C = (), E = (), S = ()> {
    pub(crate) parser: A,
    pub(crate) separator: B,
    pub(crate) at_least: usize,
    pub(crate) at_most: Option<usize>,
    pub(crate) allow_leading: bool,
    pub(crate) allow_trailing: bool,
    pub(crate) phantom: PhantomData<(C, E, S, I)>,
}

impl<A: Copy, B: Copy, I: ?Sized, C, E, S> Copy for SeparatedBy<A, B, I, C, E, S> {}
impl<A: Clone, B: Clone, I: ?Sized, C, E, S> Clone for SeparatedBy<A, B, I, C, E, S> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            separator: self.separator.clone(),
            at_least: self.at_least,
            at_most: self.at_most,
            allow_leading: self.allow_leading,
            allow_trailing: self.allow_trailing,
            phantom: PhantomData,
        }
    }
}

impl<
        'a,
        A: Parser<'a, I, E, S>,
        B: Parser<'a, I, E, S>,
        I: Input + ?Sized,
        C,
        E: Error<I>,
        S: 'a,
    > SeparatedBy<A, B, I, C, E, S>
{
    pub fn at_least(self, at_least: usize) -> Self {
        Self { at_least, ..self }
    }

    pub fn at_most(self, at_most: usize) -> Self {
        Self {
            at_most: Some(at_most),
            ..self
        }
    }

    pub fn exactly(self, exactly: usize) -> Self {
        Self {
            at_least: exactly,
            at_most: Some(exactly),
            ..self
        }
    }

    pub fn allow_leading(self) -> Self {
        Self {
            allow_leading: true,
            ..self
        }
    }

    pub fn allow_trailing(self) -> Self {
        Self {
            allow_trailing: true,
            ..self
        }
    }

    pub fn collect<D: Container<A::Output>>(self) -> SeparatedBy<A, B, I, D, E, S>
    where
        A: Parser<'a, I, E, S>,
        B: Parser<'a, I, E, S>,
    {
        SeparatedBy {
            parser: self.parser,
            separator: self.separator,
            at_least: self.at_least,
            at_most: self.at_most,
            allow_leading: self.allow_leading,
            allow_trailing: self.allow_trailing,
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, S, A, B, C> Parser<'a, I, E, S> for SeparatedBy<A, B, I, C, E, S>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, E, S>,
    B: Parser<'a, I, E, S>,
    C: Container<A::Output>,
{
    type Output = C;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E> {
        // STEPS:
        // 1. If allow_leading -> Consume separator if there
        //    if Ok  -> continue
        //    if Err -> rewind and continue
        //
        // 2. Consume item
        //    if Ok -> add to output and continue
        //    if Err && count >= self.at_least -> rewind and return output
        //    if Err && count < self.at_least -> rewind and return Err
        //
        // 3. Consume separator
        //    if Ok => continue
        //    if Err && count >= self.at_least => rewind and break
        //    if Err && count < self.at_least => rewind and return Err
        //
        // 4. Consume item
        //    if Ok && count >= self.at_most -> add to output and break
        //    if Ok && count < self.at_most -> add to output and continue
        //    if Err && count >= self.at_least => rewind and break
        //    if Err && count < self.at_least => rewind and return Err
        //
        // 5. Goto 3 until 'break'
        //
        // 6. If allow_trailing -> Consume separator
        //    if Ok -> continue
        //    if Err -> rewind and continue
        //
        // 7. Return output

        // Setup
        let mut count = 0;
        let mut output = M::bind::<C, _>(|| C::default());

        // Step 1
        if self.allow_leading {
            let before_separator = inp.save();
            if let Err(_) = self.separator.go::<Check>(inp) {
                inp.rewind(before_separator);
            }
        }

        // Step 2
        let before = inp.save();
        match self.parser.go::<M>(inp) {
            Ok(item) => {
                output = M::map(output, |mut output: C| {
                    M::map(item, |item| output.push(item));
                    output
                });
                count += 1;
            }
            Err(..) if self.at_least == 0 => {
                inp.rewind(before);
                return Ok(output);
            }
            Err(err) => {
                inp.rewind(before);
                return Err(err);
            }
        }

        loop {
            // Step 3
            let before_separator = inp.save();
            match self.separator.go::<Check>(inp) {
                Ok(..) => {
                    // Do nothing
                }
                Err(err) if count < self.at_least => {
                    inp.rewind(before_separator);
                    return Err(err);
                }
                Err(..) => {
                    inp.rewind(before_separator);
                    break;
                }
            }

            // Step 4
            match self.parser.go::<M>(inp) {
                Ok(item) => {
                    output = M::map(output, |mut output: C| {
                        M::map(item, |item| output.push(item));
                        output
                    });
                    count += 1;

                    if self.at_most.map_or(false, |max| count >= max) {
                        break;
                    } else {
                        continue;
                    }
                }
                Err(err) if count < self.at_least => {
                    // We have errored before we have reached the count,
                    // and therefore should return this error, as we are
                    // still expecting items
                    inp.rewind(before_separator);
                    return Err(err);
                }
                Err(..) => {
                    // We are not expecting any more items, so it is okay
                    // for it to fail, though if it does, we shouldn't have
                    // consumed the separator, so we need to rewind to it.
                    inp.rewind(before_separator);
                    break;
                }
            }

            // Step 5
            // continue
        }

        // Step 6
        if self.allow_trailing {
            let before_separator = inp.save();
            if let Err(_) = self.separator.go::<Check>(inp) {
                inp.rewind(before_separator);
            }
        }

        // Step 7
        Ok(output)
    }

    go_extra!();
}

#[derive(Copy, Clone)]
pub struct OrNot<A> {
    pub(crate) parser: A,
}

impl<'a, I, E, S, A> Parser<'a, I, E, S> for OrNot<A>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, E, S>,
{
    type Output = Option<A::Output>;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E> {
        let before = inp.save();
        Ok(match self.parser.go::<M>(inp) {
            Ok(o) => M::map::<A::Output, _, _>(o, Some),
            Err(_) => {
                inp.rewind(before);
                M::bind::<Option<A::Output>, _>(|| None)
            }
        })
    }

    go_extra!();
}

pub trait ContainerExactly<T, const N: usize> {
    type Uninit;
    fn uninit() -> Self::Uninit;
    fn write(uninit: &mut Self::Uninit, i: usize, item: T);
    unsafe fn drop_before(uninit: &mut Self::Uninit, i: usize);
    unsafe fn take(uninit: Self::Uninit) -> Self;
}

impl<T, const N: usize> ContainerExactly<T, N> for () {
    type Uninit = ();
    fn uninit() -> Self::Uninit {}
    fn write(_: &mut Self::Uninit, _: usize, _: T) {}
    unsafe fn drop_before(_: &mut Self::Uninit, _: usize) {}
    unsafe fn take(_: Self::Uninit) -> Self {}
}

impl<T, const N: usize> ContainerExactly<T, N> for [T; N] {
    type Uninit = [MaybeUninit<T>; N];
    fn uninit() -> Self::Uninit {
        MaybeUninit::uninit_array()
    }
    fn write(uninit: &mut Self::Uninit, i: usize, item: T) {
        uninit[i].write(item);
    }
    unsafe fn drop_before(uninit: &mut Self::Uninit, i: usize) {
        uninit[..i].iter_mut().for_each(|o| o.assume_init_drop());
    }
    unsafe fn take(uninit: Self::Uninit) -> Self {
        MaybeUninit::array_assume_init(uninit)
    }
}

#[derive(Copy, Clone)]
pub struct RepeatedExactly<A, C, const N: usize> {
    pub(crate) parser: A,
    pub(crate) phantom: PhantomData<C>,
}

impl<A, C, const N: usize> RepeatedExactly<A, C, N> {
    pub fn collect<'a, I: Input, E: Error<I>, S: 'a, D: ContainerExactly<A::Output, N>>(
        self,
    ) -> RepeatedExactly<A, D, N>
    where
        A: Parser<'a, I, E, S>,
    {
        RepeatedExactly {
            parser: self.parser,
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, S, A, C, const N: usize> Parser<'a, I, E, S> for RepeatedExactly<A, C, N>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, E, S>,
    C: ContainerExactly<A::Output, N>,
{
    type Output = C;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E> {
        let mut i = 0;
        let mut output = M::bind(|| C::uninit());
        loop {
            let before = inp.save();
            match self.parser.go::<M>(inp) {
                Ok(out) => {
                    output = M::map(output, |mut output| {
                        M::map(out, |out| {
                            C::write(&mut output, i, out);
                        });
                        output
                    });
                    i += 1;
                    if i == N {
                        // SAFETY: All entries with an index < i are filled
                        break Ok(M::map(output, |output| unsafe { C::take(output) }));
                    }
                }
                Err(e) => {
                    inp.rewind(before);
                    // SAFETY: All entries with an index < i are filled
                    unsafe {
                        M::map(output, |mut output| C::drop_before(&mut output, i));
                    }
                    break Err(e);
                }
            }
        }
    }

    go_extra!();
}

#[derive(Copy, Clone)]
pub struct SeparatedByExactly<A, B, C, const N: usize> {
    pub(crate) parser: A,
    pub(crate) separator: B,
    pub(crate) allow_leading: bool,
    pub(crate) allow_trailing: bool,
    pub(crate) phantom: PhantomData<C>,
}

impl<A, B, C, const N: usize> SeparatedByExactly<A, B, C, N> {
    pub fn allow_leading(self) -> Self {
        Self {
            allow_leading: true,
            ..self
        }
    }

    pub fn allow_trailing(self) -> Self {
        Self {
            allow_trailing: true,
            ..self
        }
    }

    pub fn collect<'a, I: Input, E: Error<I>, S: 'a, D: ContainerExactly<A::Output, N>>(
        self,
    ) -> SeparatedByExactly<A, B, D, N>
    where
        A: Parser<'a, I, E, S>,
    {
        SeparatedByExactly {
            parser: self.parser,
            separator: self.separator,
            allow_leading: self.allow_leading,
            allow_trailing: self.allow_trailing,
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, S, A, B, C, const N: usize> Parser<'a, I, E, S> for SeparatedByExactly<A, B, C, N>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, E, S>,
    B: Parser<'a, I, E, S>,
    C: ContainerExactly<A::Output, N>,
{
    type Output = [A::Output; N];

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E> {
        if self.allow_leading {
            let before_separator = inp.save();
            if let Err(_) = self.separator.go::<Check>(inp) {
                inp.rewind(before_separator);
            }
        }

        let mut i = 0;
        let mut output = MaybeUninit::uninit_array();
        loop {
            let before = inp.save();
            match self.parser.go::<M>(inp) {
                Ok(out) => {
                    output[i].write(out);
                    i += 1;
                    if i == N {
                        if self.allow_trailing {
                            let before_separator = inp.save();
                            if let Err(_) = self.separator.go::<Check>(inp) {
                                inp.rewind(before_separator);
                            }
                        }

                        // SAFETY: All entries with an index < i are filled
                        break Ok(M::array::<A::Output, N>(unsafe {
                            MaybeUninit::array_assume_init(output)
                        }));
                    } else {
                        let before_separator = inp.save();
                        if let Err(e) = self.separator.go::<Check>(inp) {
                            inp.rewind(before_separator);
                            // SAFETY: All entries with an index < i are filled
                            output[..i]
                                .iter_mut()
                                .for_each(|o| unsafe { o.assume_init_drop() });
                            break Err(e);
                        }
                    }
                }
                Err(e) => {
                    inp.rewind(before);
                    // SAFETY: All entries with an index < i are filled
                    output[..i]
                        .iter_mut()
                        .for_each(|o| unsafe { o.assume_init_drop() });
                    break Err(e);
                }
            }
        }
    }

    go_extra!();
}

pub struct Foldr<P, F, A, B, E = (), S = ()> {
    pub(crate) parser: P,
    pub(crate) folder: F,
    pub(crate) phantom: PhantomData<(A, B, E, S)>,
}

impl<P: Copy, F: Copy, A, B, E, S> Copy for Foldr<P, F, A, B, E, S> {}
impl<P: Clone, F: Clone, A, B, E, S> Clone for Foldr<P, F, A, B, E, S> {
    fn clone(&self) -> Self {
        Foldr {
            parser: self.parser.clone(),
            folder: self.folder.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, P, F, A, B, E, S> Parser<'a, I, E, S> for Foldr<P, F, A, B, E, S>
where
    I: Input + ?Sized,
    P: Parser<'a, I, E, S, Output = (A, B)>,
    E: Error<I>,
    S: 'a,
    A: IntoIterator,
    A::IntoIter: DoubleEndedIterator,
    F: Fn(A::Item, B) -> B,
{
    type Output = B;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E>
    where
        Self: Sized,
    {
        self.parser.go::<M>(inp).map(|out| {
            M::map(out, |(init, end)| {
                init.into_iter().rfold(end, |b, a| (self.folder)(a, b))
            })
        })
    }

    go_extra!();
}

pub struct Foldl<P, F, A, B, E = (), S = ()> {
    pub(crate) parser: P,
    pub(crate) folder: F,
    pub(crate) phantom: PhantomData<(A, B, E, S)>,
}

impl<P: Copy, F: Copy, A, B, E, S> Copy for Foldl<P, F, A, B, E, S> {}
impl<P: Clone, F: Clone, A, B, E, S> Clone for Foldl<P, F, A, B, E, S> {
    fn clone(&self) -> Self {
        Foldl {
            parser: self.parser.clone(),
            folder: self.folder.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, P, F, A, B, E, S> Parser<'a, I, E, S> for Foldl<P, F, A, B, E, S>
where
    I: Input + ?Sized,
    P: Parser<'a, I, E, S, Output = (A, B)>,
    E: Error<I>,
    S: 'a,
    B: IntoIterator,
    F: Fn(A, B::Item) -> A,
{
    type Output = A;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E>
    where
        Self: Sized,
    {
        self.parser.go::<M>(inp).map(|out| {
            M::map(out, |(head, tail)| {
                tail.into_iter().fold(head, &self.folder)
            })
        })
    }

    go_extra!();
}

#[derive(Copy, Clone)]
pub struct Rewind<A> {
    pub(crate) parser: A,
}

impl<'a, I, E, S, A> Parser<'a, I, E, S> for Rewind<A>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, E, S>,
{
    type Output = A::Output;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E> {
        let before = inp.save();
        match self.parser.go::<M>(inp) {
            Ok(o) => {
                inp.rewind(before);
                Ok(o)
            }
            Err(e) => Err(e),
        }
    }

    go_extra!();
}

#[derive(Copy, Clone)]
pub struct MapErr<A, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
}

impl<'a, I, E, S, A, F> Parser<'a, I, E, S> for MapErr<A, F>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, E, S>,
    F: Fn(E) -> E,
{
    type Output = A::Output;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E>
    where
        Self: Sized,
    {
        self.parser.go::<M>(inp).map_err(|mut e| {
            e.err = (self.mapper)(e.err);
            e
        })
    }

    go_extra!();
}

#[derive(Copy, Clone)]
pub struct MapErrWithSpan<A, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
}

impl<'a, I, E, S, A, F> Parser<'a, I, E, S> for MapErrWithSpan<A, F>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, E, S>,
    F: Fn(E, I::Span) -> E,
{
    type Output = A::Output;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E>
    where
        Self: Sized,
    {
        let start = inp.save();
        self.parser.go::<M>(inp).map_err(|mut e| {
            let span = inp.span_since(start);
            e.err = (self.mapper)(e.err, span);
            e
        })
    }

    go_extra!();
}

#[derive(Copy, Clone)]
pub struct MapErrWithState<A, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
}

impl<'a, I, E, S, A, F> Parser<'a, I, E, S> for MapErrWithState<A, F>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, E, S>,
    F: Fn(E, I::Span, &mut S) -> E,
{
    type Output = A::Output;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E>
    where
        Self: Sized,
    {
        let start = inp.save();
        self.parser.go::<M>(inp).map_err(|mut e| {
            let span = inp.span_since(start);
            e.err = (self.mapper)(e.err, span, inp.state());
            e
        })
    }

    go_extra!();
}

// TODO: Finish implementing this once full error recovery is implemented
/*#[derive(Copy, Clone)]
pub struct Validate<A, F> {
    pub(crate) parser: A,
    pub(crate) validator: F,
}

impl<'a, I, E, S, A, F> Parser<'a, I, E, S> for Validate<A, F>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, E, S>,
    F: Fn(E, I::Span, &mut dyn FnMut(E)) -> E,
{
    type Output = A::Output;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E>
    where
        Self: Sized,
    {
        let before = inp.save();
        self.parser.go::<Emit>(inp).and_then(|out| {
            let span = inp.span_since(before);
            match (self.validator)(out, span, todo!()) {
                Ok(out) => Ok(M::bind(|| out)),
                Err(e) => Err(Located::at(inp.last_pos(), e)),
            }
        })
    }

    go_extra!();
}*/

#[derive(Copy, Clone)]
pub struct OrElse<A, F> {
    pub(crate) parser: A,
    pub(crate) or_else: F,
}

impl<'a, I, E, S, A, F> Parser<'a, I, E, S> for OrElse<A, F>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, E, S>,
    F: Fn(E) -> Result<A::Output, E>,
{
    type Output = A::Output;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E>
    where
        Self: Sized,
    {
        match self.parser.go::<M>(inp) {
            Ok(o) => Ok(o),
            Err(err) => match (self.or_else)(err.err) {
                Err(e) => Err(Located {
                    pos: err.pos,
                    err: e,
                }),
                Ok(out) => Ok(M::bind(|| out)),
            },
        }
    }

    go_extra!();
}

#[cfg(test)]
mod tests {
    use crate::zero_copy::prelude::*;

    #[test]
    fn separated_by_at_least() {
        let parser = just::<_, _, (), ()>('-')
            .separated_by(just(','))
            .at_least(3)
            .collect();

        assert_eq!(parser.parse("-,-,-"), (Some(vec!['-', '-', '-']), vec![]));
    }

    #[test]
    fn separated_by_at_least_without_leading() {
        let parser = just::<_, _, (), ()>('-')
            .separated_by(just(','))
            .at_least(3)
            .collect::<Vec<_>>();

        // Is empty means no errors
        assert!(!parser.parse(",-,-,-").1.is_empty());
    }

    #[test]
    fn separated_by_at_least_without_trailing() {
        let parser = just::<_, _, (), ()>('-')
            .separated_by(just(','))
            .at_least(3)
            .collect::<Vec<_>>()
            .then(end());

        // Is empty means no errors
        assert!(!parser.parse("-,-,-,").1.is_empty());
    }

    #[test]
    fn separated_by_at_least_with_leading() {
        let parser = just::<_, _, (), ()>('-')
            .separated_by(just(','))
            .allow_leading()
            .at_least(3)
            .collect();

        assert_eq!(parser.parse(",-,-,-"), (Some(vec!['-', '-', '-']), vec![]));
        assert!(!parser.parse(",-,-").1.is_empty());
    }

    #[test]
    fn separated_by_at_least_with_trailing() {
        let parser = just::<_, _, (), ()>('-')
            .separated_by(just(','))
            .allow_trailing()
            .at_least(3)
            .collect();

        assert_eq!(parser.parse("-,-,-,"), (Some(vec!['-', '-', '-']), vec![]));
        assert!(!parser.parse("-,-,").1.is_empty());
    }

    #[test]
    fn separated_by_leaves_last_separator() {
        let parser = just::<_, _, (), ()>('-')
            .separated_by(just(','))
            .collect::<Vec<_>>()
            .chain(just(','));
        assert_eq!(
            parser.parse("-,-,-,"),
            (Some(vec!['-', '-', '-', ',']), vec![])
        )
    }
}
