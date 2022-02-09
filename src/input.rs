#![allow(missing_docs)]

use core::{
    cmp::Eq,
    hash::Hash,
    ops::{Range, RangeFrom},
    marker::PhantomData,
    lazy::OnceCell,
};
use crate::Rc;
use std::collections::HashMap;
#[cfg(feature = "regex")]
use ::regex as regex_crate;

pub trait Span {
    type Context;
    type Offset;
}

impl<T> Span for Range<T> {
    type Context = ();
    type Offset = T;
}

impl<Ctx, T> Span for (Ctx, Range<T>) {
    type Context = Ctx;
    type Offset = T;
}

pub trait Input {
    type Offset: Copy;
    type Token;
    type Span: Span;

    fn start(&self) -> Self::Offset;

    fn next(&self, offset: Self::Offset) -> (Self::Offset, Option<Self::Token>);

    fn span(&self, range: Range<Self::Offset>) -> Self::Span;
}

pub trait SliceInput: Input {
    type Slice: ?Sized;

    fn slice(&self, range: Range<Self::Offset>) -> &Self::Slice;
    fn slice_from(&self, from: RangeFrom<Self::Offset>) -> &Self::Slice;
}

// Implemented by inputs that reference a string slice and use byte indices as their offset.
pub trait StrInput<C: Char>: Input<Offset = usize, Token = C> + SliceInput<Slice = C::Slice> {}

impl Input for str {
    type Offset = usize;
    type Token = char;
    type Span = Range<usize>;

    fn start(&self) -> Self::Offset { 0 }

    fn next(&self, offset: Self::Offset) -> (Self::Offset, Option<Self::Token>) {
        if offset < self.len() {
            // TODO: Can we `unwrap_unchecked` here?
            let c = unsafe { self.get_unchecked(offset..).chars().next().unwrap() };
            (offset + c.len_utf8(), Some(c))
        } else {
            (offset, None)
        }
    }

    fn span(&self, range: Range<Self::Offset>) -> Self::Span { range }
}

impl StrInput<char> for str {}

impl SliceInput for str {
    type Slice = str;

    fn slice(&self, range: Range<Self::Offset>) -> &Self::Slice { &self[range] }
    fn slice_from(&self, from: RangeFrom<Self::Offset>) -> &Self::Slice { &self[from] }
}

pub struct ContextSrc<'a, Ctx>(pub Ctx, pub &'a str);

impl<'a, Ctx: Clone> Input for ContextSrc<'a, Ctx> {
    type Offset = usize;
    type Token = char;
    type Span = (Ctx, Range<usize>);

    fn start(&self) -> Self::Offset { 0 }

    fn next(&self, offset: Self::Offset) -> (Self::Offset, Option<Self::Token>) { self.1.next(offset) }

    fn span(&self, range: Range<Self::Offset>) -> Self::Span { (self.0.clone(), range) }
}

impl<'a, Ctx: Clone> SliceInput for ContextSrc<'a, Ctx> {
    type Slice = str;

    fn slice(&self, range: Range<Self::Offset>) -> &Self::Slice { <str as SliceInput>::slice(&*self.1, range) }
    fn slice_from(&self, from: RangeFrom<Self::Offset>) -> &Self::Slice { <str as SliceInput>::slice_from(&*self.1, from) }
}

impl<'a, Ctx: Clone> StrInput<char> for ContextSrc<'a, Ctx> {}

impl<T: Clone> Input for [T] {
    type Offset = usize;
    type Token = T;
    type Span = Range<usize>;

    fn start(&self) -> Self::Offset { 0 }

    fn next(&self, offset: Self::Offset) -> (Self::Offset, Option<Self::Token>) {
        if let Some(tok) = self.get(offset) {
            (offset + 1, Some(tok.clone()))
        } else {
            (offset, None)
        }
    }

    fn span(&self, range: Range<Self::Offset>) -> Self::Span { range }
}

impl StrInput<u8> for [u8] {}

impl<T: Clone> SliceInput for [T] {
    type Slice = [T];

    fn slice(&self, range: Range<Self::Offset>) -> &Self::Slice { &self[range] }
    fn slice_from(&self, from: RangeFrom<Self::Offset>) -> &Self::Slice { &self[from] }
}

pub struct InputRef<'a, 'parse, I: Input + ?Sized, S> {
    input: &'a I,
    offset: I::Offset,
    state: &'parse mut S,
}

impl<'a, 'parse, I: Input + ?Sized, S> InputRef<'a, 'parse, I, S> {
    fn new(input: &'a I, state: &'parse mut S) -> Self {
        Self {
            input,
            offset: input.start(),
            state,
        }
    }

    pub fn save(&mut self) -> I::Offset { self.offset }
    pub fn rewind(&mut self, offset: I::Offset) { self.offset = offset; }

    pub fn skip_while<F: FnMut(&I::Token) -> bool>(&mut self, mut f: F) {
        loop {
            let before = self.save();
            match self.next() {
                (_, Some(c)) if f(&c) => {},
                (_, Some(_) | None) => {
                    self.rewind(before);
                    break;
                },
            }
        }
    }

    pub fn next(&mut self) -> (I::Offset, Option<I::Token>) {
        let (offset, token) = self.input.next(self.offset);
        self.offset = offset;
        (offset, token)
    }

    pub fn slice(&self, range: Range<I::Offset>) -> &'a I::Slice
    where
        I: SliceInput,
    { self.input.slice(range) }

    pub fn slice_from(&self, from: RangeFrom<I::Offset>) -> &'a I::Slice
    where
        I: SliceInput,
    { self.input.slice_from(from) }

    pub fn slice_trailing(&self) -> &'a I::Slice
    where
        I: SliceInput,
    { self.input.slice_from(self.offset..) }

    pub fn span_since(&self, before: I::Offset) -> I::Span { self.input.span(before..self.offset) }

    pub fn skip_bytes<C>(&mut self, skip: usize)
    where
        C: Char,
        I: StrInput<C>,
    { self.offset += skip; }
}

pub trait Error<T> {
    fn create() -> Self;
}

impl<T> Error<T> for () {
    fn create() -> Self {}
}

pub type PResult<M, O, E> = Result<<M as Mode>::Output<O>, E>;

pub trait Mode {
    type Output<T>;
    fn bind<T, F: FnOnce() -> T>(f: F) -> Self::Output<T>;
    fn map<T, U, F: FnOnce(T) -> U>(x: Self::Output<T>, f: F) -> Self::Output<U>;
    fn combine<T, U, V, F: FnOnce(T, U) -> V>(x: Self::Output<T>, y: Self::Output<U>, f: F) -> Self::Output<V>;
    fn array<T, const N: usize>(x: [Self::Output<T>; N]) -> Self::Output<[T; N]>;

    fn invoke<'a, I: Input + ?Sized, E: Error<I::Token>, S, P: Parser<'a, I, E, S> + ?Sized>(parser: &P, inp: &mut InputRef<'a, '_, I, S>) -> PResult<Self, P::Output, E>;
}

pub struct Emit;
impl Mode for Emit {
    type Output<T> = T;
    fn bind<T, F: FnOnce() -> T>(f: F) -> Self::Output<T> { f() }
    fn map<T, U, F: FnOnce(T) -> U>(x: Self::Output<T>, f: F) -> Self::Output<U> { f(x) }
    fn combine<T, U, V, F: FnOnce(T, U) -> V>(x: Self::Output<T>, y: Self::Output<U>, f: F) -> Self::Output<V> { f(x, y) }
    fn array<T, const N: usize>(x: [Self::Output<T>; N]) -> Self::Output<[T; N]> { x }

    fn invoke<'a, I: Input + ?Sized, E: Error<I::Token>, S, P: Parser<'a, I, E, S> + ?Sized>(parser: &P, inp: &mut InputRef<'a, '_, I, S>) -> PResult<Self, P::Output, E> {
        parser.go_emit(inp)
    }
}

pub struct Check;
impl Mode for Check {
    type Output<T> = ();
    fn bind<T, F: FnOnce() -> T>(_: F) -> Self::Output<T> {}
    fn map<T, U, F: FnOnce(T) -> U>(x: Self::Output<T>, f: F) -> Self::Output<U> {}
    fn combine<T, U, V, F: FnOnce(T, U) -> V>(x: Self::Output<T>, y: Self::Output<U>, f: F) -> Self::Output<V> {}
    fn array<T, const N: usize>(x: [Self::Output<T>; N]) -> Self::Output<[T; N]> {}

    fn invoke<'a, I: Input + ?Sized, E: Error<I::Token>, S, P: Parser<'a, I, E, S> + ?Sized>(parser: &P, inp: &mut InputRef<'a, '_, I, S>) -> PResult<Self, P::Output, E> {
        parser.go_check(inp)
    }
}

pub trait Parser<'a, I: Input + ?Sized, E: Error<I::Token> = (), S: 'a = ()> {
    type Output;

    fn parse(&self, input: &'a I) -> Result<Self::Output, E>
    where
        Self: Sized,
        S: Default,
    {
        self.go::<Emit>(&mut InputRef::new(input, &mut S::default()))
    }

    fn parse_with_state(&self, input: &'a I, state: &mut S) -> Result<Self::Output, E>
    where
        Self: Sized,
    {
        self.go::<Emit>(&mut InputRef::new(input, state))
    }

    fn check(&self, input: &'a I) -> Result<(), E>
    where
        Self: Sized,
        S: Default,
    {
        self.go::<Check>(&mut InputRef::new(input, &mut S::default()))
    }

    #[doc(hidden)]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, S>) -> PResult<M, Self::Output, E> where Self: Sized;

    #[doc(hidden)]
    fn go_emit(&self, inp: &mut InputRef<'a, '_, I, S>) -> PResult<Emit, Self::Output, E>;
    #[doc(hidden)]
    fn go_check(&self, inp: &mut InputRef<'a, '_, I, S>) -> PResult<Check, Self::Output, E>;

    fn map_slice<O, F: Fn(&'a I::Slice) -> O>(self, f: F) -> MapSlice<Self, F, E, S>
    where
        Self: Sized,
        I: SliceInput,
        I::Slice: 'a,
    {
        MapSlice { parser: self, mapper: f, phantom: PhantomData }
    }

    fn map<O, F: Fn(Self::Output) -> O>(self, f: F) -> Map<Self, F>
    where
        Self: Sized,
    {
        Map { parser: self, mapper: f }
    }

    fn map_with_span<O, F: Fn(Self::Output, I::Span) -> O>(self, f: F) -> MapWithSpan<Self, F>
    where
        Self: Sized,
    {
        MapWithSpan { parser: self, mapper: f }
    }

    fn ignored(self) -> Ignored<Self, E, S>
    where
        Self: Sized,
    {
        Ignored { parser: self, to: (), phantom: PhantomData }
    }

    fn to<O: Clone>(self, to: O) -> To<Self, O>
    where
        Self: Sized,
    {
        To { parser: self, to, phantom: PhantomData }
    }

    fn then<B: Parser<'a, I, E, S>>(self, other: B) -> Then<Self, B, E, S>
    where
        Self: Sized,
    {
        Then { parser_a: self, parser_b: other, phantom: PhantomData }
    }

    fn delimited_by<B: Parser<'a, I, E, S>, C: Parser<'a, I, E, S>>(self, start: B, end: C) -> DelimitedBy<Self, B, C>
    where
        Self: Sized,
    {
        DelimitedBy { parser: self, start, end }
    }

    fn or<B: Parser<'a, I, E, S, Output = Self::Output>>(self, other: B) -> Or<Self, B>
    where
        Self: Sized,
    {
        Or { parser_a: self, parser_b: other }
    }

    fn or_not(self) -> OrNot<Self>
    where
        Self: Sized,
    {
        OrNot { parser: self }
    }

    fn repeated(self) -> Repeated<Self, I, (), E, S>
    where
        Self: Sized,
    {
        Repeated { parser: self, at_least: 0, phantom: PhantomData }
    }

    fn repeated_exactly<const N: usize>(self) -> RepeatedExactly<Self, N>
    where
        Self: Sized,
    {
        RepeatedExactly { parser: self }
    }

    fn padded(self) -> Padded<Self>
    where
        Self: Sized,
        I: Input,
        I::Token: Char,
    {
        Padded { parser: self }
    }

    fn boxed(self) -> Boxed<'a, I, Self::Output, E, S> where Self: Sized + 'a {
        Boxed { inner: Rc::new(self) }
    }
}

macro_rules! go_extra {
    () => {
        fn go_emit(&self, inp: &mut InputRef<'a, '_, I, S>) -> PResult<Emit, Self::Output, E> {
            Parser::<I, E, S>::go::<Emit>(self, inp)
        }
        fn go_check(&self, inp: &mut InputRef<'a, '_, I, S>) -> PResult<Check, Self::Output, E> {
            Parser::<I, E, S>::go::<Check>(self, inp)
        }
    };
}

#[derive(Copy, Clone)]
pub struct End<I: ?Sized>(PhantomData<I>);

pub fn end<I: Input + ?Sized>() -> End<I> {
    End(PhantomData)
}

impl<'a, I, E, S> Parser<'a, I, E, S> for End<I>
where
    I: Input + ?Sized,
    E: Error<I::Token>,
    S: 'a,
{
    type Output = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, S>) -> PResult<M, Self::Output, E> {
        match inp.next() {
            (_, None) => Ok(M::bind(|| ())),
            (_, Some(_)) => Err(E::create()),
        }
    }

    go_extra!();
}

pub trait Seq<T> {
    type Iter<'a>: Iterator<Item = T>;
    fn iter(&self) -> Self::Iter<'_>;
}

impl<T: Clone> Seq<T> for T {
    type Iter<'a> = core::iter::Once<T>;
    fn iter(&self) -> Self::Iter<'_> { core::iter::once(self.clone()) }
}

impl<T: Clone, const N: usize> Seq<T> for [T; N] {
    type Iter<'a> = core::array::IntoIter<T, N>;
    fn iter(&self) -> Self::Iter<'_> { core::array::IntoIter::new(self.clone()) }
}

impl<'b, T: Clone, const N: usize> Seq<T> for &'b [T; N] {
    type Iter<'a> = core::array::IntoIter<T, N>;
    fn iter(&self) -> Self::Iter<'_> { core::array::IntoIter::new((*self).clone()) }
}

impl Seq<char> for str {
    type Iter<'a> = core::str::Chars<'a>;
    fn iter(&self) -> Self::Iter<'_> { self.chars() }
}

// impl<'b, T, C: Container<T>> Container<T> for &'b C {
//     type Iter<'a> = C::Iter<'a>;
//     fn iter(&self) -> Self::Iter<'_> { (*self).iter() }
// }

pub struct Just<T, I: ?Sized, E = (), S = ()> {
    seq: T,
    phantom: PhantomData<(E, S, I)>,
}

impl<T: Copy, I: ?Sized, E, S> Copy for Just<T, I, E, S> {}
impl<T: Clone, I: ?Sized, E, S> Clone for Just<T, I, E, S> {
    fn clone(&self) -> Self {
        Self {
            seq: self.seq.clone(),
            phantom: PhantomData,
        }
    }
}

pub fn just<T, I, E, S>(seq: T) -> Just<T, I, E, S>
where
    I: Input + ?Sized,
    E: Error<I::Token>,
    I::Token: PartialEq,
    T: Seq<I::Token> + Clone,
{
    Just {
        seq,
        phantom: PhantomData,
    }
}

impl<'a, I, E, S, T> Parser<'a, I, E, S> for Just<T, I, E, S>
where
    I: Input + ?Sized,
    E: Error<I::Token>,
    S: 'a,
    I::Token: PartialEq,
    T: Seq<I::Token> + Clone,
{
    type Output = T;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, S>) -> PResult<M, Self::Output, E> {
        let mut items = self.seq.iter();
        loop {
            match items.next() {
                Some(next) => match inp.next() {
                    (_, Some(tok)) if next == tok => {},
                    (_, Some(_) | None) => break Err(E::create()),
                },
                None => break Ok(M::bind(|| self.seq.clone())),
            }
        }
    }

    go_extra!();
}

#[cfg(feature = "regex")]
pub struct Regex<C: Char, I: ?Sized, E = (), S = ()> {
    regex: C::Regex,
    phantom: PhantomData<(E, S, I)>,
}

#[cfg(feature = "regex")]
pub fn regex<C: Char, I: ?Sized, E, S>(pattern: &str) -> Regex<C, I, E, S> {
    Regex {
        regex: C::new_regex(pattern),
        phantom: PhantomData,
    }
}

#[cfg(feature = "regex")]
impl<'a, C, I, E, S> Parser<'a, I, E, S> for Regex<C, I, E, S>
where
    C: Char,
    C::Slice: 'a,
    I: Input + StrInput<C> + ?Sized,
    E: Error<I::Token>,
    S: 'a,
{
    type Output = &'a C::Slice;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, S>) -> PResult<M, Self::Output, E> {
        C::match_regex(&self.regex, inp.slice_trailing())
            .map(|len| {
                let before = inp.save();
                inp.skip_bytes(len);
                let after = inp.save();
                M::bind(|| inp.slice(before..after))
            })
            .ok_or_else(|| E::create())
    }

    go_extra!();
}

pub struct MapSlice<A, F, E = (), S = ()> {
    parser: A,
    mapper: F,
    phantom: PhantomData<(E, S)>,
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
    E: Error<I::Token>,
    S: 'a,
    I::Slice: 'a,
    A: Parser<'a, I, E, S>,
    F: Fn(&'a I::Slice) -> O,
{
    type Output = O;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, S>) -> PResult<M, Self::Output, E> {
        let before = inp.save();
        match self.parser.go::<Check>(inp) {
            Ok(_) => {
                let after = inp.save();
                Ok(M::bind(|| (self.mapper)(inp.slice(before..after))))
            },
            Err(e) => Err(e),
        }
    }

    go_extra!();
}

pub struct Filter<F, I: ?Sized> {
    filter: F,
    phantom: PhantomData<I>,
}

impl<F: Copy, I: ?Sized> Copy for Filter<F, I> {}
impl<F: Clone, I: ?Sized> Clone for Filter<F, I> {
    fn clone(&self) -> Self {
        Self {
            filter: self.filter.clone(),
            phantom: PhantomData,
        }
    }
}

pub fn filter<F: Fn(&I::Token) -> bool, I: Input + ?Sized>(filter: F) -> Filter<F, I> {
    Filter { filter, phantom: PhantomData }
}

impl<'a, I, E, S, F> Parser<'a, I, E, S> for Filter<F, I>
where
    I: Input + ?Sized,
    E: Error<I::Token>,
    S: 'a,
    F: Fn(&I::Token) -> bool,
{
    type Output = I::Token;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, S>) -> PResult<M, Self::Output, E> {
        match inp.next() {
            (_, Some(tok)) if (self.filter)(&tok) => Ok(M::bind(|| tok)),
            (_, Some(_) | None) => Err(E::create()),
        }
    }

    go_extra!();
}

#[derive(Copy, Clone)]
pub struct Map<A, F> {
    parser: A,
    mapper: F,
}

impl<'a, I, E, S, A, F, O> Parser<'a, I, E, S> for Map<A, F>
where
    I: Input + ?Sized,
    E: Error<I::Token>,
    S: 'a,
    A: Parser<'a, I, E, S>,
    F: Fn(A::Output) -> O,
{
    type Output = O;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, S>) -> PResult<M, Self::Output, E> {
        self.parser.go::<M>(inp)
            .map(|out| M::map(out, &self.mapper))
    }

    go_extra!();
}

#[derive(Copy, Clone)]
pub struct MapWithSpan<A, F> {
    parser: A,
    mapper: F,
}

impl<'a, I, E, S, A, F, O> Parser<'a, I, E, S> for MapWithSpan<A, F>
where
    I: Input + ?Sized,
    E: Error<I::Token>,
    S: 'a,
    A: Parser<'a, I, E, S>,
    F: Fn(A::Output, I::Span) -> O,
{
    type Output = O;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, S>) -> PResult<M, Self::Output, E> {
        let before = inp.save();
        self.parser.go::<M>(inp).map(|out| M::map(out, |out| {
            let span = inp.span_since(before);
            (self.mapper)(out, span)
        }))
    }

    go_extra!();
}

pub struct To<A, O, E = (), S = ()> {
    parser: A,
    to: O,
    phantom: PhantomData<(E, S)>,
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
    E: Error<I::Token>,
    S: 'a,
    A: Parser<'a, I, E, S>,
    O: Clone,
{
    type Output = O;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, S>) -> PResult<M, Self::Output, E> {
        self.parser.go::<Check>(inp)
            .map(|_| M::bind(|| self.to.clone()))
    }

    go_extra!();
}

pub type Ignored<A, E = (), S = ()> = To<A, (), E, S>;

pub struct Then<A, B, E = (), S = ()> {
    parser_a: A,
    parser_b: B,
    phantom: PhantomData<(E, S)>,
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
    E: Error<I::Token>,
    S: 'a,
    A: Parser<'a, I, E, S>,
    B: Parser<'a, I, E, S>,
{
    type Output = (A::Output, B::Output);

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, S>) -> PResult<M, Self::Output, E> {
        let a = self.parser_a.go::<M>(inp)?;
        let b = self.parser_b.go::<M>(inp)?;
        Ok(M::combine(a, b, |a, b| (a, b)))
    }

    go_extra!();
}

#[derive(Copy, Clone)]
pub struct DelimitedBy<A, B, C> {
    parser: A,
    start: B,
    end: C,
}

impl<'a, I, E, S, A, B, C> Parser<'a, I, E, S> for DelimitedBy<A, B, C>
where
    I: Input + ?Sized,
    E: Error<I::Token>,
    S: 'a,
    A: Parser<'a, I, E, S>,
    B: Parser<'a, I, E, S>,
    C: Parser<'a, I, E, S>,
{
    type Output = A::Output;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, S>) -> PResult<M, Self::Output, E> {
        let _ = self.start.go::<Check>(inp)?;
        let b = self.parser.go::<M>(inp)?;
        let _ = self.end.go::<Check>(inp)?;
        Ok(b)
    }

    go_extra!();
}

#[derive(Copy, Clone)]
pub struct Or<A, B> {
    parser_a: A,
    parser_b: B,
}

impl<'a, I, E, S, A, B> Parser<'a, I, E, S> for Or<A, B>
where
    I: Input + ?Sized,
    E: Error<I::Token>,
    S: 'a,
    A: Parser<'a, I, E, S>,
    B: Parser<'a, I, E, S, Output = A::Output>,
{
    type Output = A::Output;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, S>) -> PResult<M, Self::Output, E> {
        let before = inp.save();
        match self.parser_a.go::<M>(inp) {
            Ok(out) => Ok(out),
            Err(_) => {
                inp.rewind(before);
                self.parser_b.go::<M>(inp)
            },
        }
    }

    go_extra!();
}

#[derive(Copy, Clone)]
pub struct Choice<T, O> {
    parsers: T,
    phantom: PhantomData<O>,
}

pub fn choice<T, O>(parsers: T) -> Choice<T, O> {
    Choice { parsers, phantom: PhantomData }
}

macro_rules! impl_for_tuple {
    () => {};
    ($head:ident $($X:ident)*) => {
        impl_for_tuple!($($X)*);
        impl_for_tuple!(~ $head $($X)*);
    };
    (~ $($X:ident)*) => {
        #[allow(unused_variables, non_snake_case)]
        impl<'a, I, E, S, $($X),*, O> Parser<'a, I, E, S> for Choice<($($X,)*), O>
        where
            I: Input + ?Sized,
            E: Error<I::Token>,
            S: 'a,
            $($X: Parser<'a, I, E, S, Output = O>),*
        {
            type Output = O;

            fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, S>) -> PResult<M, Self::Output, E> {
                let before = inp.save();

                let Choice { parsers: ($($X,)*), .. } = self;

                $(
                    match $X.go::<M>(inp) {
                        Ok(out) => return Ok(out),
                        Err(_) => inp.rewind(before),
                    };
                )*

                Err(E::create())
            }

            go_extra!();
        }
    };
}

impl_for_tuple!(A_ B_ C_ D_ E_ F_ G_ H_ I_ J_ K_ L_ M_ N_ O_ P_ Q_ S_ T_ U_ V_ W_ X_ Y_ Z_);

pub trait Char: Sized {
    type Slice: ?Sized + StrInput<Self> + 'static;

    #[cfg(feature = "regex")]
    type Regex;

    #[cfg(feature = "regex")]
    #[doc(hidden)]
    fn new_regex(pattern: &str) -> Self::Regex;
    #[cfg(feature = "regex")]
    #[doc(hidden)]
    fn match_regex(regex: &Self::Regex, trailing: &Self::Slice) -> Option<usize>;

    fn is_whitespace(&self) -> bool;
}

impl Char for char {
    type Slice = str;

    #[cfg(feature = "regex")]
    type Regex = regex_crate::Regex;

    #[cfg(feature = "regex")]
    fn new_regex(pattern: &str) -> Self::Regex {
        regex_crate::Regex::new(pattern).expect("Failed to compile regex")
    }
    #[cfg(feature = "regex")]
    #[inline]
    fn match_regex(regex: &Self::Regex, trailing: &Self::Slice) -> Option<usize> {
        regex
            .find(trailing)
            .filter(|m| m.start() == 0)
            .map(|m| m.end())
    }

    fn is_whitespace(&self) -> bool { (*self).is_whitespace() }
}

impl Char for u8 {
    type Slice = [u8];

    #[cfg(feature = "regex")]
    type Regex = regex_crate::bytes::Regex;

    #[cfg(feature = "regex")]
    fn new_regex(pattern: &str) -> Self::Regex {
        regex_crate::bytes::Regex::new(pattern).expect("Failed to compile regex")
    }
    #[cfg(feature = "regex")]
    #[inline]
    fn match_regex(regex: &Self::Regex, trailing: &Self::Slice) -> Option<usize> {
        regex
            .find(trailing)
            .filter(|m| m.start() == 0)
            .map(|m| m.end())
    }

    fn is_whitespace(&self) -> bool { self.is_ascii_whitespace() }
}

#[derive(Clone)]
pub struct Padded<A> {
    parser: A,
}

impl<'a, I, E, S, A> Parser<'a, I, E, S> for Padded<A>
where
    I: Input + ?Sized,
    E: Error<I::Token>,
    S: 'a,
    I::Token: Char,
    A: Parser<'a, I, E, S>,
{
    type Output = A::Output;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, S>) -> PResult<M, Self::Output, E> {
        inp.skip_while(|c| c.is_whitespace());
        let out = self.parser.go::<M>(inp)?;
        inp.skip_while(|c| c.is_whitespace());
        Ok(out)
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

impl<K: Eq + Hash, V> Container<(K, V)> for HashMap<K, V> {
    fn push(&mut self, (key, value): (K, V)) {
        (*self).insert(key, value);
    }
}

pub struct Repeated<A, I: ?Sized, C = (), E = (), S = ()> {
    parser: A,
    at_least: usize,
    phantom: PhantomData<(C, E, S, I)>,
}

impl<A: Copy, I: ?Sized, C, E, S> Copy for Repeated<A, I, C, E, S> {}
impl<A: Clone, I: ?Sized, C, E, S> Clone for Repeated<A, I, C, E, S> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            at_least: self.at_least,
            phantom: PhantomData,
        }
    }
}

impl<'a, A: Parser<'a, I, E, S>, I: Input + ?Sized, C, E: Error<I::Token>, S: 'a> Repeated<A, I, C, E, S> {
    pub fn at_least(self, at_least: usize) -> Self {
        Self { at_least, .. self }
    }

    pub fn collect<D: Container<A::Output>>(self) -> Repeated<A, I, D, E, S>
        where A: Parser<'a, I, E, S>
    {
        Repeated {
            parser: self.parser,
            at_least: self.at_least,
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, S, A, C> Parser<'a, I, E, S> for Repeated<A, I, C>
where
    I: Input + ?Sized,
    E: Error<I::Token>,
    S: 'a,
    A: Parser<'a, I, E, S>,
    C: Container<A::Output>,
{
    type Output = C;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, S>) -> PResult<M, Self::Output, E> {
        let mut count = 0;
        let mut output = M::bind::<C, _>(|| C::default());
        loop {
            let before = inp.save();
            match self.parser.go::<M>(inp) {
                Ok(out) => {
                    output = M::map(output, |mut output| {
                        M::map(out, |out| output.push(out));
                        output
                    });
                    count += 1;
                },
                Err(e) => {
                    inp.rewind(before);
                    break if count >= self.at_least {
                        Ok(output)
                    } else {
                        Err(e)
                    };
                },
            }
        }
    }

    go_extra!();
}

#[derive(Copy, Clone)]
pub struct OrNot<A> {
    parser: A,
}

impl<'a, I, E, S, A> Parser<'a, I, E, S> for OrNot<A>
where
    I: Input + ?Sized,
    E: Error<I::Token>,
    S: 'a,
    A: Parser<'a, I, E, S>,
{
    type Output = Option<A::Output>;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, S>) -> PResult<M, Self::Output, E> {
        let before = inp.save();
        Ok(match self.parser.go::<M>(inp) {
            Ok(o) => M::map(o, Some),
            Err(_) => {
                inp.rewind(before);
                M::bind(|| None)
            },
        })
    }

    go_extra!();
}

#[derive(Copy, Clone)]
pub struct RepeatedExactly<A, const N: usize> {
    parser: A,
}

impl<'a, I, E, S, A, const N: usize> Parser<'a, I, E, S> for RepeatedExactly<A, N>
where
    I: Input + ?Sized,
    E: Error<I::Token>,
    S: 'a,
    A: Parser<'a, I, E, S>,
{
    type Output = [A::Output; N];

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, S>) -> PResult<M, Self::Output, E> {
        use std::mem::MaybeUninit;

        let mut i = 0;
        let mut output = MaybeUninit::uninit_array();
        loop {
            let before = inp.save();
            match self.parser.go::<M>(inp) {
                Ok(out) => {
                    output[i].write(out);
                    i += 1;
                    if i == N {
                        // SAFETY: All entries with an index < i are filled
                        break Ok(M::array(unsafe { MaybeUninit::array_assume_init(output) }));
                    }
                },
                Err(e) => {
                    inp.rewind(before);
                    // SAFETY: All entries with an index < i are filled
                    output[..i]
                        .iter_mut()
                        .for_each(|o| unsafe { o.assume_init_drop() });
                    break Err(e);
                },
            }
        }
    }

    go_extra!();
}

pub struct RecursiveInner<'a, I: ?Sized, O, E, S = ()> {
    this: Rc<OnceCell<Self>>,
    parser: Box<dyn Parser<'a, I, E, S, Output = O> + 'a>,
}

pub struct Recursive<'a, I: ?Sized, O, E, S = ()> {
    inner: Rc<OnceCell<RecursiveInner<'a, I, O, E, S>>>,
}

impl<'a, I: ?Sized, O, E, S> Clone for Recursive<'a, I, O, E, S> {
    fn clone(&self) -> Self {
        Self { inner: self.inner.clone() }
    }
}

pub fn recursive<'a, I: Input + ?Sized, E: Error<I::Token>, S, A: Parser<'a, I, E, S> + 'a, F: FnOnce(Recursive<'a, I, A::Output, E, S>) -> A>(f: F) -> Recursive<'a, I, A::Output, E, S> {
    let recursive = Recursive { inner: Rc::new(OnceCell::new()) };
    recursive.inner
        .set(RecursiveInner {
            this: recursive.inner.clone(),
            parser: Box::new(f(recursive.clone())),
        })
        .ok()
        .expect("recursive parser already declared");
    recursive
}

impl<'a, I, E, S, O> Parser<'a, I, E, S> for Recursive<'a, I, O, E, S>
where
    I: Input + ?Sized,
    E: Error<I::Token>,
    S: 'a,
{
    type Output = O;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, S>) -> PResult<M, Self::Output, E> {
        M::invoke(&*self.inner
            .get()
            .expect("recursive parser used before definition")
            .parser, inp)
    }

    go_extra!();
}

pub struct Boxed<'a, I: ?Sized, O, E, S = ()> {
    inner: Rc<dyn Parser<'a, I, E, S, Output = O> + 'a>,
}

impl<'a, I: ?Sized, E, O, S> Clone for Boxed<'a, I, O, E, S> {
    fn clone(&self) -> Self {
        Self { inner: self.inner.clone() }
    }
}

impl<'a, I, E, S, O> Parser<'a, I, E, S> for Boxed<'a, I, O, E, S>
where
    I: Input + ?Sized,
    E: Error<I::Token>,
    S: 'a,
{
    type Output = O;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, S>) -> PResult<M, Self::Output, E> {
        M::invoke(&*self.inner, inp)
    }

    go_extra!();
}

#[test]
fn zero_copy() {
    #[derive(Clone)]
    enum TokenTest {
        Root,
        Branch(Box<Self>),
    }

    fn parser2() -> impl Parser<'static, str, Output = TokenTest> {
        recursive(|token| {
            token
                .delimited_by(just('c'), just('c'))
                .map(Box::new)
                .map(TokenTest::Branch)
                .or(just('!').to(TokenTest::Root))
        })
    }

    #[derive(PartialEq, Debug)]
    enum Token<'a> {
        Ident(&'a str),
        String(&'a str),
    }

    type Span = (i32, Range<usize>);

    fn parser<'a>() -> impl Parser<'a, ContextSrc<'a, i32>, Output = [(Span, Token<'a>); 6]> {
        let ident = filter(|c: &char| c.is_alphanumeric())
            .repeated()
            .at_least(1)
            .map_slice(Token::Ident);

        let string = just('"')
            .then(filter(|c: &char| *c != '"').repeated())
            .then(just('"'))
            .map_slice(Token::String);

        ident
            .or(string)
            .map_with_span(|token, span| (span, token))
            .padded()
            .repeated_exactly()
    }

    assert_eq!(
        parser().parse(&ContextSrc(42, r#"hello "world" these are "test" tokens"#)),
        Ok([
            ((42, 0..5), Token::Ident("hello")),
            ((42, 6..13), Token::String("\"world\"")),
            ((42, 14..19), Token::Ident("these")),
            ((42, 20..23), Token::Ident("are")),
            ((42, 24..30), Token::String("\"test\"")),
            ((42, 31..37), Token::Ident("tokens")),
        ]),
    );
}

#[cfg(feature = "regex")]
#[test]
fn regex_parser() {

    fn parser<'a, C: Char>() -> impl Parser<'a, C::Slice, Output = Vec<&'a C::Slice>> {
        regex("[a-zA-Z_][a-zA-Z0-9_]*")
            .padded()
            .repeated()
            .collect()
    }

    assert_eq!(
        parser::<char>().parse("hello world this works"),
        Ok(vec![
            "hello",
            "world",
            "this",
            "works",
        ]),
    );

    assert_eq!(
        parser::<u8>().parse(b"hello world this works" as &[_]),
        Ok(vec![
            b"hello" as &[_],
            b"world" as &[_],
            b"this" as &[_],
            b"works" as &[_],
        ]),
    );
}

#[test]
fn unicode_str() {
    let input = "🄯🄚🹠🴎🄐🝋🰏🄂🬯🈦g🸵🍩🕔🈳2🬙🨞🅢🭳🎅h🵚🧿🏩🰬k🠡🀔🈆🝹🤟🉗🴟📵🰄🤿🝜🙘🹄5🠻🡉🱖🠓";
    let mut state = ();
    let mut input = InputRef::new(input, &mut state);

    while let (_, Some(c)) = input.next() {
        std::hint::black_box(c);
    }
}
