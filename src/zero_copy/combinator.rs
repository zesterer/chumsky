//! Combinators that allow combining and extending existing parsers.
//!
//! *“Ford... you're turning into a penguin. Stop it.”*
//!
//! Although it's *sometimes* useful to be able to name their type, most of these parsers are much easier to work with
//! when accessed through their respective methods on [`Parser`].

use super::*;
use core::mem::MaybeUninit;
use hashbrown::HashSet;

// TODO: Remove this when MaybeUninit transforms to/from arrays stabilize in any form
trait MaybeUninitExt<T>: Sized {
    /// Identical to the unstable [`MaybeUninit::uninit_array`]
    fn uninit_array<const N: usize>() -> [Self; N];

    /// Identical to the unstable [`MaybeUninit::array_assume_init`]
    unsafe fn array_assume_init<const N: usize>(uninit: [Self; N]) -> [T; N];
}

impl<T> MaybeUninitExt<T> for MaybeUninit<T> {
    fn uninit_array<const N: usize>() -> [Self; N] {
        // SAFETY: Output type is entirely uninhabited - IE, it's made up entirely of `MaybeUninit`
        unsafe { MaybeUninit::uninit().assume_init() }
    }

    unsafe fn array_assume_init<const N: usize>(uninit: [Self; N]) -> [T; N] {
        let out = (&uninit as *const [Self; N] as *const [T; N]).read();
        core::mem::forget(uninit);
        out
    }
}

/// See [`Parser::map_slice`].
pub struct MapSlice<'a, A, I, O, E, S, F, U>
where
    I: Input + SliceInput + ?Sized,
    E: Error<I>,
    S: 'a,
    I::Slice: 'a,
    A: Parser<'a, I, O, E, S>,
    F: Fn(&'a I::Slice) -> U,
{
    pub(crate) parser: A,
    pub(crate) mapper: F,
    pub(crate) phantom: PhantomData<(&'a I::Slice, O, E, S)>,
}

impl<'a, A: Copy, I, O, E, S, F: Copy, U> Copy for MapSlice<'a, A, I, O, E, S, F, U>
where
    I: Input + SliceInput + Sized,
    E: Error<I>,
    S: 'a,
    I::Slice: 'a,
    A: Parser<'a, I, O, E, S>,
    F: Fn(&'a I::Slice) -> U,
{
}
impl<'a, A: Clone, I, O, E, S, F: Clone, U> Clone for MapSlice<'a, A, I, O, E, S, F, U>
where
    I: Input + SliceInput + ?Sized,
    E: Error<I>,
    S: 'a,
    I::Slice: 'a,
    A: Parser<'a, I, O, E, S>,
    F: Fn(&'a I::Slice) -> U,
{
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            mapper: self.mapper.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, O, E, S, A, F, U> Parser<'a, I, U, E, S> for MapSlice<'a, A, I, O, E, S, F, U>
where
    I: Input + SliceInput + ?Sized,
    E: Error<I>,
    S: 'a,
    I::Slice: 'a,
    A: Parser<'a, I, O, E, S>,
    F: Fn(&'a I::Slice) -> U,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, U, E> {
        let before = inp.save();
        self.parser.go::<Check>(inp)?;
        let after = inp.save();

        Ok(M::bind(|| (self.mapper)(inp.slice(before..after))))
    }

    go_extra!(U);
}

/// See [`Parser::filter`].
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

impl<'a, A, I, O, E, S, F> Parser<'a, I, O, E, S> for Filter<A, F>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, O, E, S>,
    F: Fn(&O) -> bool,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, O, E> {
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

    go_extra!(O);
}

/// See [`Parser::map`].
#[derive(Copy, Clone)]
pub struct Map<A, OA, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
    pub(crate) phantom: PhantomData<OA>,
}

impl<'a, I, O, E, S, A, OA, F> Parser<'a, I, O, E, S> for Map<A, OA, F>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, OA, E, S>,
    F: Fn(OA) -> O,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, O, E> {
        self.parser
            .go::<M>(inp)
            .map(|out| M::map(out, &self.mapper))
    }

    go_extra!(O);
}

/// See [`Parser::map_with_span`].
#[derive(Copy, Clone)]
pub struct MapWithSpan<A, OA, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
    pub(crate) phantom: PhantomData<OA>,
}

impl<'a, I, O, E, S, A, OA, F> Parser<'a, I, O, E, S> for MapWithSpan<A, OA, F>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, OA, E, S>,
    F: Fn(OA, I::Span) -> O,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, O, E> {
        let before = inp.save();
        self.parser.go::<M>(inp).map(|out| {
            M::map(out, |out| {
                let span = inp.span_since(before);
                (self.mapper)(out, span)
            })
        })
    }

    go_extra!(O);
}

/// See [`Parser::map_with_state`].
#[derive(Copy, Clone)]
pub struct MapWithState<A, OA, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
    pub(crate) phantom: PhantomData<OA>,
}

impl<'a, I, O, E, S, A, OA, F> Parser<'a, I, O, E, S> for MapWithState<A, OA, F>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, OA, E, S>,
    F: Fn(OA, I::Span, &mut S) -> O,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, O, E> {
        let before = inp.save();
        self.parser.go::<Emit>(inp).map(|out| {
            M::bind(|| {
                let span = inp.span_since(before);
                let state = inp.state();
                (self.mapper)(out, span, state)
            })
        })
    }

    go_extra!(O);
}

/// See [`Parser::try_map`].
#[derive(Copy, Clone)]
pub struct TryMap<A, OA, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
    pub(crate) phantom: PhantomData<OA>,
}

impl<'a, I, O, E, S, A, OA, F> Parser<'a, I, O, E, S> for TryMap<A, OA, F>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, OA, E, S>,
    F: Fn(OA, I::Span) -> Result<O, E>,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, O, E> {
        let before = inp.save();
        self.parser.go::<Emit>(inp).and_then(|out| {
            let span = inp.span_since(before);
            match (self.mapper)(out, span) {
                Ok(out) => Ok(M::bind(|| out)),
                Err(e) => Err(Located::at(inp.last_pos(), e)),
            }
        })
    }

    go_extra!(O);
}

/// See [`Parser::try_map_with_state`].
#[derive(Copy, Clone)]
pub struct TryMapWithState<A, OA, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
    pub(crate) phantom: PhantomData<OA>,
}

impl<'a, I, O, E, S, A, OA, F> Parser<'a, I, O, E, S> for TryMapWithState<A, OA, F>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, OA, E, S>,
    F: Fn(OA, I::Span, &mut S) -> Result<O, E>,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, O, E> {
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

    go_extra!(O);
}

/// See [`Parser::to`].
pub struct To<A, OA, O, E = (), S = ()> {
    pub(crate) parser: A,
    pub(crate) to: O,
    pub(crate) phantom: PhantomData<(OA, E, S)>,
}

impl<A: Copy, OA, O: Copy, E, S> Copy for To<A, OA, O, E, S> {}
impl<A: Clone, OA, O: Clone, E, S> Clone for To<A, OA, O, E, S> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            to: self.to.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, O, E, S, A, OA> Parser<'a, I, O, E, S> for To<A, OA, O, E, S>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, OA, E, S>,
    O: Clone,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, O, E> {
        self.parser
            .go::<Check>(inp)
            .map(|_| M::bind(|| self.to.clone()))
    }

    go_extra!(O);
}

/// See [`Parser::ignored`].
pub struct Ignored<A, OA> {
    pub(crate) parser: A,
    pub(crate) phantom: PhantomData<OA>,
}

impl<A: Copy, OA> Copy for Ignored<A, OA> {}
impl<A: Clone, OA> Clone for Ignored<A, OA> {
    fn clone(&self) -> Self {
        Ignored { parser: self.parser.clone(), phantom: PhantomData }
    }
}

impl<'a, I, E, S, A, OA> Parser<'a, I, (), E, S> for Ignored<A, OA>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, OA, E, S>,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, (), E> {
        self.parser.go::<Check>(inp).map(|_| M::bind(|| ()))
    }

    go_extra!(());
}

/// See [`Parser::then`].
pub struct Then<A, B, OA, OB, E = (), S = ()> {
    pub(crate) parser_a: A,
    pub(crate) parser_b: B,
    pub(crate) phantom: PhantomData<(OA, OB, E, S)>,
}

impl<A: Copy, B: Copy, OA, OB, E, S> Copy for Then<A, B, OA, OB, E, S> {}
impl<A: Clone, B: Clone, OA, OB, E, S> Clone for Then<A, B, OA, OB, E, S> {
    fn clone(&self) -> Self {
        Self {
            parser_a: self.parser_a.clone(),
            parser_b: self.parser_b.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, S, A, B, OA, OB> Parser<'a, I, (OA, OB), E, S> for Then<A, B, OA, OB, E, S>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, OA, E, S>,
    B: Parser<'a, I, OB, E, S>,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, (OA, OB), E> {
        let a = self.parser_a.go::<M>(inp)?;
        let b = self.parser_b.go::<M>(inp)?;
        Ok(M::combine(a, b, |a: OA, b: OB| (a, b)))
    }

    go_extra!((OA, OB));
}

/// See [`Parser::ignore_then`].
pub struct IgnoreThen<A, B, OA, E = (), S = ()> {
    pub(crate) parser_a: A,
    pub(crate) parser_b: B,
    pub(crate) phantom: PhantomData<(OA, E, S)>,
}

impl<A: Copy, B: Copy, OA, E, S> Copy for IgnoreThen<A, B, OA, E, S> {}
impl<A: Clone, B: Clone, OA, E, S> Clone for IgnoreThen<A, B, OA, E, S> {
    fn clone(&self) -> Self {
        Self {
            parser_a: self.parser_a.clone(),
            parser_b: self.parser_b.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, S, A, B, OA, OB> Parser<'a, I, OB, E, S> for IgnoreThen<A, B, OA, E, S>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, OA, E, S>,
    B: Parser<'a, I, OB, E, S>,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, OB, E> {
        let _a = self.parser_a.go::<Check>(inp)?;
        let b = self.parser_b.go::<M>(inp)?;
        Ok(M::map(b, |b: OB| b))
    }

    go_extra!(OB);
}

/// See [`Parser::then_ignore`].
pub struct ThenIgnore<A, B, OB, E = (), S = ()> {
    pub(crate) parser_a: A,
    pub(crate) parser_b: B,
    pub(crate) phantom: PhantomData<(OB, E, S)>,
}

impl<A: Copy, B: Copy, OB, E, S> Copy for ThenIgnore<A, B, OB, E, S> {}
impl<A: Clone, B: Clone, OB, E, S> Clone for ThenIgnore<A, B, OB, E, S> {
    fn clone(&self) -> Self {
        Self {
            parser_a: self.parser_a.clone(),
            parser_b: self.parser_b.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, S, A, B, OA, OB> Parser<'a, I, OA, E, S> for ThenIgnore<A, B, OB, E, S>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, OA, E, S>,
    B: Parser<'a, I, OB, E, S>,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, OA, E> {
        let a = self.parser_a.go::<M>(inp)?;
        let _b = self.parser_b.go::<Check>(inp)?;
        Ok(M::map(a, |a: OA| a))
    }

    go_extra!(OA);
}

/// See [`Parser::then_with`].
pub struct ThenWith<A, B, OA, F, I: ?Sized, E = (), S = ()> {
    pub(crate) parser: A,
    pub(crate) then: F,
    pub(crate) phantom: PhantomData<(B, OA, E, S, I)>,
}

impl<A: Copy, B, OA, F: Copy, I: ?Sized, E, S> Copy for ThenWith<A, B, OA, F, I, E, S> {}
impl<A: Clone, B, OA, F: Clone, I: ?Sized, E, S> Clone for ThenWith<A, B, OA, F, I, E, S> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            then: self.then.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, S, A, B, OA, OB, F> Parser<'a, I, OB, E, S> for ThenWith<A, B, OA, F, I, E, S>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, OA, E, S>,
    B: Parser<'a, I, OB, E, S>,
    F: Fn(OA) -> B,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, OB, E> {
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

    go_extra!(OB);
}

/// See [`Parser::delimited_by`].
#[derive(Copy, Clone)]
pub struct DelimitedBy<A, B, C, OB, OC> {
    pub(crate) parser: A,
    pub(crate) start: B,
    pub(crate) end: C,
    pub(crate) phantom: PhantomData<(OB, OC)>,
}

impl<'a, I, E, S, A, B, C, OA, OB, OC> Parser<'a, I, OA, E, S> for DelimitedBy<A, B, C, OB, OC>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, OA, E, S>,
    B: Parser<'a, I, OB, E, S>,
    C: Parser<'a, I, OC, E, S>,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, OA, E> {
        let _ = self.start.go::<Check>(inp)?;
        let a = self.parser.go::<M>(inp)?;
        let _ = self.end.go::<Check>(inp)?;
        Ok(a)
    }

    go_extra!(OA);
}

/// See [`Parser::padded_by`].
#[derive(Copy, Clone)]
pub struct PaddedBy<A, B, OB> {
    pub(crate) parser: A,
    pub(crate) padding: B,
    pub(crate) phantom: PhantomData<OB>,
}

impl<'a, I, E, S, A, B, OA, OB> Parser<'a, I, OA, E, S> for PaddedBy<A, B, OB>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, OA, E, S>,
    B: Parser<'a, I, OB, E, S>,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, OA, E> {
        let _ = self.padding.go::<Check>(inp)?;
        let a = self.parser.go::<M>(inp)?;
        let _ = self.padding.go::<Check>(inp)?;
        Ok(a)
    }

    go_extra!(OA);
}

/// See [`Parser::or`].
#[derive(Copy, Clone)]
pub struct Or<A, B> {
    pub(crate) parser_a: A,
    pub(crate) parser_b: B,
}

impl<'a, I, O, E, S, A, B> Parser<'a, I, O, E, S> for Or<A, B>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, O, E, S>,
    B: Parser<'a, I, O, E, S>,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, O, E> {
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

    go_extra!(O);
}

/// See [`Parser::recover_with`].
#[derive(Copy, Clone)]
pub struct RecoverWith<A, F> {
    pub(crate) parser: A,
    pub(crate) fallback: F,
}

impl<'a, I, O, E, S, A, F> Parser<'a, I, O, E, S> for RecoverWith<A, F>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, O, E, S>,
    F: Parser<'a, I, O, E, S>,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, O, E> {
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

    go_extra!(O);
}

/// A utility trait for types that can be constructed from a series of output values
pub trait Container<T>: Default {
    /// Add a value to the end of this container
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

/// See [`Parser::repeated`].
// FIXME: why C, E, S have default values?
pub struct Repeated<A, OA, I: ?Sized, C = (), E = (), S = ()> {
    pub(crate) parser: A,
    pub(crate) at_least: usize,
    pub(crate) at_most: Option<usize>,
    pub(crate) phantom: PhantomData<(OA, C, E, S, I)>,
}

impl<A: Copy, OA, I: ?Sized, C, E, S> Copy for Repeated<A, OA, I, C, E, S> {}
impl<A: Clone, OA, I: ?Sized, C, E, S> Clone for Repeated<A, OA, I, C, E, S> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            at_least: self.at_least,
            at_most: self.at_most,
            phantom: PhantomData,
        }
    }
}

impl<'a, A, OA, I, C, E, S> Repeated<A, OA, I, C, E, S>
where
    A: Parser<'a, I, OA, E, S>,
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
{
    /// Require that the pattern appear at least a minimum number of times.
    pub fn at_least(self, at_least: usize) -> Self {
        Self { at_least, ..self }
    }

    /// Require that the pattern appear at most a maximum number of times.
    pub fn at_most(self, at_most: usize) -> Self {
        Self {
            at_most: Some(at_most),
            ..self
        }
    }

    /// Require that the pattern appear exactly the given number of times. If the value provided
    /// is constant, consider instead using [`Parser::repeated_exactly`]
    ///
    /// ```
    /// # use chumsky::zero_copy::prelude::*;
    /// let ring = just::<_, _, Simple<str>, ()>('O');
    ///
    /// let for_the_elves = ring
    ///     .repeated()
    ///     .exactly(3)
    ///     .collect::<Vec<_>>();
    ///
    /// let for_the_dwarves = ring
    ///     .repeated()
    ///     .exactly(6)
    ///     .collect::<Vec<_>>();
    ///
    /// let for_the_humans = ring
    ///     .repeated()
    ///     .exactly(9)
    ///     .collect::<Vec<_>>();
    ///
    /// let for_sauron = ring
    ///     .repeated()
    ///     .exactly(1)
    ///     .collect::<Vec<_>>();
    ///
    /// let rings = for_the_elves
    ///     .then(for_the_dwarves)
    ///     .then(for_the_humans)
    ///     .then(for_sauron)
    ///     .then_ignore(end());
    ///
    /// assert!(rings.parse("OOOOOOOOOOOOOOOOOO").has_errors()); // Too few rings!
    /// assert!(rings.parse("OOOOOOOOOOOOOOOOOOOO").has_errors()); // Too many rings!
    /// // The perfect number of rings
    /// assert_eq!(
    ///     rings.parse("OOOOOOOOOOOOOOOOOOO"),
    ///     ParseResult::Ok(((((vec!['O'; 3]), vec!['O'; 6]), vec!['O'; 9]), vec!['O'; 1])),
    /// );
    /// ````
    pub fn exactly(self, exactly: usize) -> Self {
        Self {
            at_least: exactly,
            at_most: Some(exactly),
            ..self
        }
    }

    /// Set the type of [`Container`] to collect into.
    pub fn collect<D: Container<OA>>(self) -> Repeated<A, OA, I, D, E, S>
    where
        A: Parser<'a, I, OA, E, S>,
    {
        Repeated {
            parser: self.parser,
            at_least: self.at_least,
            at_most: self.at_most,
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, S, A, OA, C> Parser<'a, I, C, E, S> for Repeated<A, OA, I, C, E, S>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, OA, E, S>,
    C: Container<OA>,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, C, E> {
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

    go_extra!(C);
}

/// See [`Parser::separated_by`].
pub struct SeparatedBy<A, B, OA, OB, I: ?Sized, C = (), E = (), S = ()> {
    pub(crate) parser: A,
    pub(crate) separator: B,
    pub(crate) at_least: usize,
    pub(crate) at_most: Option<usize>,
    pub(crate) allow_leading: bool,
    pub(crate) allow_trailing: bool,
    pub(crate) phantom: PhantomData<(OA, OB, C, E, S, I)>,
}

impl<A: Copy, B: Copy, OA, OB, I: ?Sized, C, E, S> Copy for SeparatedBy<A, B, OA, OB, I, C, E, S> {}
impl<A: Clone, B: Clone, OA, OB, I: ?Sized, C, E, S> Clone
    for SeparatedBy<A, B, OA, OB, I, C, E, S>
{
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

impl<'a, A, B, OA, OB, I, C, E, S> SeparatedBy<A, B, OA, OB, I, C, E, S>
where
    A: Parser<'a, I, OA, E, S>,
    B: Parser<'a, I, OB, E, S>,
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
{
    /// Require that the pattern appear at least a minimum number of times.
    ///
    /// ```
    /// # use chumsky::zero_copy::prelude::*;
    /// let numbers = just::<_, _, Simple<str>, ()>('-')
    ///     .separated_by(just('.'))
    ///     .at_least(2)
    ///     .collect::<Vec<_>>();
    ///
    /// assert!(numbers.parse("").has_errors());
    /// assert!(numbers.parse("-").has_errors());
    /// assert_eq!(numbers.parse("-.-"), ParseResult::Ok(vec!['-', '-']));
    /// ````
    pub fn at_least(self, at_least: usize) -> Self {
        Self { at_least, ..self }
    }

    /// Require that the pattern appear at most a maximum number of times.
    ///
    /// ```
    /// # use chumsky::zero_copy::prelude::*;
    /// let row_4 = text::int::<_, _, Simple<str>, ()>(10)
    ///     .padded()
    ///     .separated_by(just(','))
    ///     .at_most(4)
    ///     .collect::<Vec<_>>();
    ///
    /// let matrix_4x4 = row_4
    ///     .separated_by(just(','))
    ///     .at_most(4)
    ///     .collect::<Vec<_>>();
    ///
    /// assert_eq!(
    ///     matrix_4x4.parse("0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15"),
    ///     ParseResult::Ok(vec![
    ///         vec!["0", "1", "2", "3"],
    ///         vec!["4", "5", "6", "7"],
    ///         vec!["8", "9", "10", "11"],
    ///         vec!["12", "13", "14", "15"],
    ///     ]),
    /// );
    /// ````
    pub fn at_most(self, at_most: usize) -> Self {
        Self {
            at_most: Some(at_most),
            ..self
        }
    }

    /// Require that the pattern appear exactly the given number of times. If the value provided is
    /// constant, consider instead using [`Parser::separated_by_exactly`].
    ///
    /// ```
    /// # use chumsky::zero_copy::prelude::*;
    /// let coordinate_3d = text::int::<_, _, Simple<str>, ()>(10)
    ///     .padded()
    ///     .separated_by(just(','))
    ///     .exactly(3)
    ///     .collect::<Vec<_>>()
    ///     .then_ignore(end());
    ///
    /// // Not enough elements
    /// assert!(coordinate_3d.parse("4, 3").has_errors());
    /// // Too many elements
    /// assert!(coordinate_3d.parse("7, 2, 13, 4").has_errors());
    /// // Just the right number of elements
    /// assert_eq!(coordinate_3d.parse("5, 0, 12"), ParseResult::Ok(vec!["5", "0", "12"]));
    /// ````
    pub fn exactly(self, exactly: usize) -> Self {
        Self {
            at_least: exactly,
            at_most: Some(exactly),
            ..self
        }
    }

    /// Allow a leading separator to appear before the first item.
    ///
    /// Note that even if no items are parsed, a leading separator *is* permitted.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::zero_copy::prelude::*;
    /// let r#enum = text::keyword::<_, _, _, Simple<str>, ()>("enum")
    ///     .padded()
    ///     .ignore_then(text::ident()
    ///         .padded()
    ///         .separated_by(just('|'))
    ///         .allow_leading()
    ///         .collect::<Vec<_>>());
    ///
    /// assert_eq!(r#enum.parse("enum True | False"), ParseResult::Ok(vec!["True", "False"]));
    /// assert_eq!(r#enum.parse("
    ///     enum
    ///     | True
    ///     | False
    /// "), ParseResult::Ok(vec!["True", "False"]));
    /// ```
    pub fn allow_leading(self) -> Self {
        Self {
            allow_leading: true,
            ..self
        }
    }

    /// Allow a trailing separator to appear after the last item.
    ///
    /// Note that if no items are parsed, no leading separator is permitted.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::zero_copy::prelude::*;
    /// let numbers = text::int::<_, _, Simple<str>, ()>(10)
    ///     .padded()
    ///     .separated_by(just(','))
    ///     .allow_trailing()
    ///     .collect::<Vec<_>>()
    ///     .delimited_by(just('('), just(')'));
    ///
    /// assert_eq!(numbers.parse("(1, 2)"), ParseResult::Ok(vec!["1", "2"]));
    /// assert_eq!(numbers.parse("(1, 2,)"), ParseResult::Ok(vec!["1", "2"]));
    /// ```
    pub fn allow_trailing(self) -> Self {
        Self {
            allow_trailing: true,
            ..self
        }
    }

    /// Set the type of [`Container`] to collect into.
    pub fn collect<D: Container<OA>>(self) -> SeparatedBy<A, B, OA, OB, I, D, E, S>
    where
        A: Parser<'a, I, OA, E, S>,
        B: Parser<'a, I, OB, E, S>,
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

impl<'a, I, E, S, A, B, OA, OB, C> Parser<'a, I, C, E, S> for SeparatedBy<A, B, OA, OB, I, C, E, S>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, OA, E, S>,
    B: Parser<'a, I, OB, E, S>,
    C: Container<OA>,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, C, E> {
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

    go_extra!(C);
}

/// See [`Parser::or_not`].
#[derive(Copy, Clone)]
pub struct OrNot<A> {
    pub(crate) parser: A,
}

impl<'a, I, O, E, S, A> Parser<'a, I, Option<O>, E, S> for OrNot<A>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, O, E, S>,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Option<O>, E> {
        let before = inp.save();
        Ok(match self.parser.go::<M>(inp) {
            Ok(o) => M::map::<O, _, _>(o, Some),
            Err(_) => {
                inp.rewind(before);
                M::bind::<Option<O>, _>(|| None)
            }
        })
    }

    go_extra!(Option<O>);
}

/// See [`Parser::not`].
#[derive(Copy, Clone)]
pub struct Not<A, OA> {
    pub(crate) parser: A,
    pub(crate) phantom: PhantomData<OA>,
}

impl<'a, I, E, S, A, OA> Parser<'a, I, (), E, S> for Not<A, OA>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, OA, E, S>,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, (), E> {
        let before = inp.save();

        let result = self.parser.go::<Check>(inp);
        inp.rewind(before);

        match result {
            Ok(_) => {
                let (at, tok) = inp.next();
                Err(Located::at(
                    at,
                    E::expected_found(None, tok, inp.span_since(before)),
                ))
            }
            Err(_) => Ok(M::bind(|| ())),
        }
    }

    go_extra!(());
}

/// See [`Parser::and_is`].
#[derive(Copy, Clone)]
pub struct AndIs<A, B, OB> {
    pub(crate) parser_a: A,
    pub(crate) parser_b: B,
    pub(crate) phantom: PhantomData<OB>,
}

impl<'a, I, E, S, A, B, OA, OB> Parser<'a, I, OA, E, S> for AndIs<A, B, OB>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, OA, E, S>,
    B: Parser<'a, I, OB, E, S>,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, OA, E> {
        let before = inp.save();
        match self.parser_a.go::<M>(inp) {
            Ok(out) => {
                // A succeeded -- go back to the beginning and try B
                let after = inp.save();
                inp.rewind(before);

                match self.parser_b.go::<Check>(inp) {
                    Ok(_) => {
                        // B succeeded -- go to the end of A and return its output
                        inp.rewind(after);
                        Ok(out)
                    }
                    Err(e) => {
                        // B failed -- go back to the beginning and fail
                        inp.rewind(before);
                        Err(e)
                    }
                }
            }
            Err(e) => {
                // A failed -- go back to the beginning and fail
                inp.rewind(before);
                Err(e)
            }
        }
    }

    go_extra!(OA);
}

/// A utility trait for types that hold a specific constant number of input values
pub trait ContainerExactly<T, const N: usize> {
    /// An uninitialized value of this container
    type Uninit;

    /// Get an uninitialized form of this container
    fn uninit() -> Self::Uninit;

    /// Write a value to a position in an uninitialized container
    fn write(uninit: &mut Self::Uninit, i: usize, item: T);

    /// Drop all values before a provided index in this container
    ///
    /// # Safety
    ///
    /// All values must be initialized, up to the provided index
    unsafe fn drop_before(uninit: &mut Self::Uninit, i: usize);

    /// Convert this container into its initialized form
    ///
    /// # Safety
    ///
    /// All values in the container must be initialized
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
        MaybeUninitExt::uninit_array()
    }
    fn write(uninit: &mut Self::Uninit, i: usize, item: T) {
        uninit[i].write(item);
    }
    unsafe fn drop_before(uninit: &mut Self::Uninit, i: usize) {
        uninit[..i].iter_mut().for_each(|o| o.assume_init_drop());
    }
    unsafe fn take(uninit: Self::Uninit) -> Self {
        MaybeUninitExt::array_assume_init(uninit)
    }
}

/// See [`Parser::repeated_exactly`].
#[derive(Copy, Clone)]
pub struct RepeatedExactly<A, OA, C, const N: usize> {
    pub(crate) parser: A,
    pub(crate) phantom: PhantomData<(OA, C)>,
}

impl<A, OA, C, const N: usize> RepeatedExactly<A, OA, C, N> {
    /// Set the type of [`ContainerExactly`] to collect into.
    pub fn collect<'a, I, E, S, D>(self) -> RepeatedExactly<A, OA, D, N>
    where
        A: Parser<'a, I, OA, E, S>,
        I: Input + ?Sized,
        E: Error<I>,
        S: 'a,
        D: ContainerExactly<OA, N>,
    {
        RepeatedExactly {
            parser: self.parser,
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, S, A, OA, C, const N: usize> Parser<'a, I, C, E, S> for RepeatedExactly<A, OA, C, N>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, OA, E, S>,
    C: ContainerExactly<OA, N>,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, C, E> {
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

    go_extra!(C);
}

/// See [`Parser::separated_by_exactly`].
#[derive(Copy, Clone)]
pub struct SeparatedByExactly<A, B, OB, C, const N: usize> {
    pub(crate) parser: A,
    pub(crate) separator: B,
    pub(crate) allow_leading: bool,
    pub(crate) allow_trailing: bool,
    pub(crate) phantom: PhantomData<(OB, C)>,
}

impl<A, B, OB, C, const N: usize> SeparatedByExactly<A, B, OB, C, N> {
    /// Allow a leading separator to appear before the first item.
    ///
    /// Note that even if no items are parsed, a leading separator *is* permitted.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::zero_copy::prelude::*;
    /// let r#enum = text::keyword::<_, _, _, Simple<str>, ()>("enum")
    ///     .padded()
    ///     .ignore_then(text::ident()
    ///         .padded()
    ///         .separated_by(just('|'))
    ///         .allow_leading()
    ///         .collect::<Vec<_>>());
    ///
    /// assert_eq!(r#enum.parse("enum True | False"), ParseResult::Ok(vec!["True", "False"]));
    /// assert_eq!(r#enum.parse("
    ///     enum
    ///     | True
    ///     | False
    /// "), ParseResult::Ok(vec!["True", "False"]));
    /// ```
    pub fn allow_leading(self) -> Self {
        Self {
            allow_leading: true,
            ..self
        }
    }

    /// Allow a trailing separator to appear after the last item.
    ///
    /// Note that if no items are parsed, no trailing separator is permitted.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::zero_copy::prelude::*;
    /// let numbers = text::int::<_, _, Simple<str>, ()>(10)
    ///     .padded()
    ///     .separated_by(just(','))
    ///     .allow_trailing()
    ///     .collect::<Vec<_>>()
    ///     .delimited_by(just('('), just(')'));
    ///
    /// assert_eq!(numbers.parse("(1, 2)"), ParseResult::Ok(vec!["1", "2"]));
    /// assert_eq!(numbers.parse("(1, 2,)"), ParseResult::Ok(vec!["1", "2"]));
    /// ```
    pub fn allow_trailing(self) -> Self {
        Self {
            allow_trailing: true,
            ..self
        }
    }

    /// Set the type of [`ContainerExactly`] to collect into.
    pub fn collect<'a, I, OA, E, S, D>(self) -> SeparatedByExactly<A, B, OB, D, N>
    where
        A: Parser<'a, I, OA, E, S>,
        I: Input,
        E: Error<I>,
        S: 'a,
        D: ContainerExactly<OA, N>,
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

// FIXME: why parser output is not C ?
impl<'a, I, E, S, A, B, OA, OB, C, const N: usize> Parser<'a, I, [OA; N], E, S>
    for SeparatedByExactly<A, B, OB, C, N>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, OA, E, S>,
    B: Parser<'a, I, OB, E, S>,
    C: ContainerExactly<OA, N>,
{
    // FIXME: why parse result output is not C ?
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, [OA; N], E> {
        if self.allow_leading {
            let before_separator = inp.save();
            if let Err(_) = self.separator.go::<Check>(inp) {
                inp.rewind(before_separator);
            }
        }

        let mut i = 0;
        let mut output = <MaybeUninit<_> as MaybeUninitExt<_>>::uninit_array();
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
                        break Ok(M::array::<OA, N>(unsafe {
                            MaybeUninitExt::array_assume_init(output)
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

    go_extra!([OA; N]);
}

/// See [`Parser::foldr`].
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

impl<'a, I, P, F, A, B, E, S> Parser<'a, I, B, E, S> for Foldr<P, F, A, B, E, S>
where
    I: Input + ?Sized,
    P: Parser<'a, I, (A, B), E, S>,
    E: Error<I>,
    S: 'a,
    A: IntoIterator,
    A::IntoIter: DoubleEndedIterator,
    F: Fn(A::Item, B) -> B,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, B, E>
    where
        Self: Sized,
    {
        self.parser.go::<M>(inp).map(|out| {
            M::map(out, |(init, end)| {
                init.into_iter().rfold(end, |b, a| (self.folder)(a, b))
            })
        })
    }

    go_extra!(B);
}

/// See [`Parser::foldl`].
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

impl<'a, I, P, F, A, B, E, S> Parser<'a, I, A, E, S> for Foldl<P, F, A, B, E, S>
where
    I: Input + ?Sized,
    P: Parser<'a, I, (A, B), E, S>,
    E: Error<I>,
    S: 'a,
    B: IntoIterator,
    F: Fn(A, B::Item) -> A,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, A, E>
    where
        Self: Sized,
    {
        self.parser.go::<M>(inp).map(|out| {
            M::map(out, |(head, tail)| {
                tail.into_iter().fold(head, &self.folder)
            })
        })
    }

    go_extra!(A);
}

/// See [`Parser::rewind`].
#[derive(Copy, Clone)]
pub struct Rewind<A> {
    pub(crate) parser: A,
}

impl<'a, I, O, E, S, A> Parser<'a, I, O, E, S> for Rewind<A>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, O, E, S>,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, O, E> {
        let before = inp.save();
        match self.parser.go::<M>(inp) {
            Ok(o) => {
                inp.rewind(before);
                Ok(o)
            }
            Err(e) => Err(e),
        }
    }

    go_extra!(O);
}

/// See [`Parser::map_err`].
#[derive(Copy, Clone)]
pub struct MapErr<A, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
}

impl<'a, I, O, E, S, A, F> Parser<'a, I, O, E, S> for MapErr<A, F>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, O, E, S>,
    F: Fn(E) -> E,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, O, E>
    where
        Self: Sized,
    {
        self.parser.go::<M>(inp).map_err(|mut e| {
            e.err = (self.mapper)(e.err);
            e
        })
    }

    go_extra!(O);
}

/// See [`Parser::map_err_with_span`].
#[derive(Copy, Clone)]
pub struct MapErrWithSpan<A, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
}

impl<'a, I, O, E, S, A, F> Parser<'a, I, O, E, S> for MapErrWithSpan<A, F>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, O, E, S>,
    F: Fn(E, I::Span) -> E,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, O, E>
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

    go_extra!(O);
}

/// See [`Parser::map_err_with_state`].
#[derive(Copy, Clone)]
pub struct MapErrWithState<A, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
}

impl<'a, I, O, E, S, A, F> Parser<'a, I, O, E, S> for MapErrWithState<A, F>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, O, E, S>,
    F: Fn(E, I::Span, &mut S) -> E,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, O, E>
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

    go_extra!(O);
}

// TODO: Finish implementing this once full error recovery is implemented
/*#[derive(Copy, Clone)]
pub struct Validate<A, F> {
    pub(crate) parser: A,
    pub(crate) validator: F,
}

impl<'a, I, O, E, S, A, F> Parser<'a, I, O, E, S> for Validate<A, F>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, O, E, S>,
    F: Fn(E, I::Span, &mut dyn FnMut(E)) -> E,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, O, E>
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

    go_extra!(O);
}*/

/// See [`Parser::or_else`].
#[derive(Copy, Clone)]
pub struct OrElse<A, F> {
    pub(crate) parser: A,
    pub(crate) or_else: F,
}

impl<'a, I, O, E, S, A, F> Parser<'a, I, O, E, S> for OrElse<A, F>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, O, E, S>,
    F: Fn(E) -> Result<O, E>,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, O, E>
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

    go_extra!(O);
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

        assert_eq!(parser.parse("-,-,-"), ParseResult::Ok(vec!['-', '-', '-']));
    }

    #[test]
    fn separated_by_at_least_without_leading() {
        let parser = just::<_, _, (), ()>('-')
            .separated_by(just(','))
            .at_least(3)
            .collect::<Vec<_>>();

        // Is empty means no errors
        assert!(parser.parse(",-,-,-").has_errors());
    }

    #[test]
    fn separated_by_at_least_without_trailing() {
        let parser = just::<_, _, (), ()>('-')
            .separated_by(just(','))
            .at_least(3)
            .collect::<Vec<_>>()
            .then(end());

        // Is empty means no errors
        assert!(parser.parse("-,-,-,").has_errors());
    }

    #[test]
    fn separated_by_at_least_with_leading() {
        let parser = just::<_, _, (), ()>('-')
            .separated_by(just(','))
            .allow_leading()
            .at_least(3)
            .collect();

        assert_eq!(parser.parse(",-,-,-"), ParseResult::Ok(vec!['-', '-', '-']));
        assert!(parser.parse(",-,-").has_errors());
    }

    #[test]
    fn separated_by_at_least_with_trailing() {
        let parser = just::<_, _, (), ()>('-')
            .separated_by(just(','))
            .allow_trailing()
            .at_least(3)
            .collect();

        assert_eq!(parser.parse("-,-,-,"), ParseResult::Ok(vec!['-', '-', '-']));
        assert!(parser.parse("-,-,").has_errors());
    }

    #[test]
    fn separated_by_leaves_last_separator() {
        let parser = just::<_, _, (), ()>('-')
            .separated_by(just(','))
            .collect::<Vec<_>>()
            .chain(just(','));
        assert_eq!(
            parser.parse("-,-,-,"),
            ParseResult::Ok(vec!['-', '-', '-', ',']),
        )
    }
}
