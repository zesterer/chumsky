//! Combinators that allow combining and extending existing parsers.
//!
//! *“Ford... you're turning into a penguin. Stop it.”*
//!
//! Although it's *sometimes* useful to be able to name their type, most of these parsers are much easier to work with
//! when accessed through their respective methods on [`Parser`].

use super::*;
use core::mem::MaybeUninit;

/// Alter the configuration of a struct using parse-time context
pub struct Configure<A, F> {
    pub(crate) parser: A,
    pub(crate) cfg: F,
}

impl<'a, In, Out, Err, State, Ctx, A, F> Parser<'a, In, Out, Err, State, Ctx> for Configure<A, F>
where
    A: Parser<'a, In, Out, Err, State, Ctx>,
    F: Fn(&mut A::Config, &mut State),
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, Out, Err>
    where
        Self: Sized,
    {
        let mut cfg = A::Config::default();
        (self.cfg)(&mut cfg, inp.state());
        self.parser.go::<M>(inp)
    }

    go_extra!(Out);
}

/// See [`Parser::map_slice`].
pub struct MapSlice<'a, A, In, Out, Err, State, Ctx, F, U>
where
    In: Input + SliceInput + ?Sized,
    Err: Error<In>,
    State: 'a,
    In::Slice: 'a,
    A: Parser<'a, In, Out, Err, State, Ctx>,
    F: Fn(&'a In::Slice) -> U,
{
    pub(crate) parser: A,
    pub(crate) mapper: F,
    pub(crate) phantom: PhantomData<(&'a In::Slice, Out, Err, State, Ctx)>,
}

impl<'a, A: Copy, In, Out, Err, State, Ctx, F: Copy, U> Copy for MapSlice<'a, A, In, Out, Err, State, Ctx, F, U>
where
    In: Input + SliceInput + Sized,
    Err: Error<In>,
    State: 'a,
    In::Slice: 'a,
    A: Parser<'a, In, Out, Err, State, Ctx>,
    F: Fn(&'a In::Slice) -> U,
{
}
impl<'a, A: Clone, In, Out, Err, State, Ctx, F: Clone, U> Clone for MapSlice<'a, A, In, Out, Err, State, Ctx, F, U>
where
    In: Input + SliceInput + ?Sized,
    Err: Error<In>,
    State: 'a,
    In::Slice: 'a,
    A: Parser<'a, In, Out, Err, State, Ctx>,
    F: Fn(&'a In::Slice) -> U,
{
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            mapper: self.mapper.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, In, Out, Err, State, Ctx, A, F, U> Parser<'a, In, U, Err, State, Ctx> for MapSlice<'a, A, In, Out, Err, State, Ctx, F, U>
where
    In: Input + SliceInput + ?Sized,
    Err: Error<In>,
    State: 'a,
    In::Slice: 'a,
    A: Parser<'a, In, Out, Err, State, Ctx>,
    F: Fn(&'a In::Slice) -> U,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, U, Err> {
        let before = inp.save();
        self.parser.go::<Check>(inp)?;
        let after = inp.save();

        Ok(M::bind(|| (self.mapper)(inp.slice(before..after))))
    }

    go_extra!(U);
}

/// See [`Parser::slice`]
pub struct Slice<A, O> {
    pub(crate) parser: A,
    pub(crate) phantom: PhantomData<O>,
}

impl<A: Copy, O> Copy for Slice<A, O> {}
impl<A: Clone, O> Clone for Slice<A, O> {
    fn clone(&self) -> Self {
        Slice {
            parser: self.parser.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, A, In, Out, Err, State, Ctx> Parser<'a, In, &'a In::Slice, Err, State, Ctx> for Slice<A, Out>
where
    A: Parser<'a, In, Out, Err, State, Ctx>,
    In: Input + SliceInput + ?Sized,
    Err: Error<In>,
    State: 'a,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, &'a In::Slice, Err>
    where
        Self: Sized,
    {
        let before = inp.save();
        self.parser.go::<Check>(inp)?;
        let after = inp.save();

        Ok(M::bind(|| inp.slice(before..after)))
    }

    go_extra!(&'a In::Slice);
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

impl<'a, A, In, Out, Err, State, Ctx, F> Parser<'a, In, Out, Err, State, Ctx> for Filter<A, F>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
    A: Parser<'a, In, Out, Err, State, Ctx>,
    F: Fn(&Out) -> bool,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, Out, Err> {
        let before = inp.save();
        self.parser.go::<Emit>(inp).and_then(|out| {
            if (self.filter)(&out) {
                Ok(M::bind(|| out))
            } else {
                let span = inp.span_since(before);
                Err(Located::at(
                    inp.last_pos(),
                    Err::expected_found(None, None, span),
                ))
            }
        })
    }

    go_extra!(Out);
}

/// See [`Parser::map`].
#[derive(Copy, Clone)]
pub struct Map<A, OA, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
    pub(crate) phantom: PhantomData<OA>,
}

impl<'a, In, Out, Err, State, Ctx, A, OA, F> Parser<'a, In, Out, Err, State, Ctx> for Map<A, OA, F>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
    A: Parser<'a, In, OA, Err, State, Ctx>,
    F: Fn(OA) -> Out,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, Out, Err> {
        self.parser
            .go::<M>(inp)
            .map(|out| M::map(out, &self.mapper))
    }

    go_extra!(Out);
}

/// See [`Parser::map_with_span`].
#[derive(Copy, Clone)]
pub struct MapWithSpan<A, OA, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
    pub(crate) phantom: PhantomData<OA>,
}

impl<'a, In, Out, Err, State, Ctx, A, OA, F> Parser<'a, In, Out, Err, State, Ctx> for MapWithSpan<A, OA, F>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
    A: Parser<'a, In, OA, Err, State, Ctx>,
    F: Fn(OA, In::Span) -> Out,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, Out, Err> {
        let before = inp.save();
        self.parser.go::<M>(inp).map(|out| {
            M::map(out, |out| {
                let span = inp.span_since(before);
                (self.mapper)(out, span)
            })
        })
    }

    go_extra!(Out);
}

/// See [`Parser::map_with_state`].
#[derive(Copy, Clone)]
pub struct MapWithState<A, OA, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
    pub(crate) phantom: PhantomData<OA>,
}

impl<'a, In, Out, Err, State, Ctx, A, OA, F> Parser<'a, In, Out, Err, State, Ctx> for MapWithState<A, OA, F>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
    A: Parser<'a, In, OA, Err, State, Ctx>,
    F: Fn(OA, In::Span, &mut State) -> Out,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, Out, Err> {
        let before = inp.save();
        self.parser.go::<Emit>(inp).map(|out| {
            M::bind(|| {
                let span = inp.span_since(before);
                let state = inp.state();
                (self.mapper)(out, span, state)
            })
        })
    }

    go_extra!(Out);
}

/// See [`Parser::try_map`].
#[derive(Copy, Clone)]
pub struct TryMap<A, OA, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
    pub(crate) phantom: PhantomData<OA>,
}

impl<'a, In, Out, Err, State, Ctx, A, OA, F> Parser<'a, In, Out, Err, State, Ctx> for TryMap<A, OA, F>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
    A: Parser<'a, In, OA, Err, State, Ctx>,
    F: Fn(OA, In::Span) -> Result<Out, Err>,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, Out, Err> {
        let before = inp.save();
        self.parser.go::<Emit>(inp).and_then(|out| {
            let span = inp.span_since(before);
            match (self.mapper)(out, span) {
                Ok(out) => Ok(M::bind(|| out)),
                Err(e) => Err(Located::at(inp.last_pos(), e)),
            }
        })
    }

    go_extra!(Out);
}

/// See [`Parser::try_map_with_state`].
#[derive(Copy, Clone)]
pub struct TryMapWithState<A, OA, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
    pub(crate) phantom: PhantomData<OA>,
}

impl<'a, In, Out, Err, State, Ctx, A, OA, F> Parser<'a, In, Out, Err, State, Ctx> for TryMapWithState<A, OA, F>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
    A: Parser<'a, In, OA, Err, State, Ctx>,
    F: Fn(OA, In::Span, &mut State) -> Result<Out, Err>,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, Out, Err> {
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

    go_extra!(Out);
}

/// See [`Parser::to`].
pub struct To<A, OA, O, E = EmptyErr, S = ()> {
    pub(crate) parser: A,
    pub(crate) to: O,
    pub(crate) phantom: PhantomData<(OA, E, S)>,
}

impl<A: Copy, OA, Out: Copy, Err, State> Copy for To<A, OA, Out, Err, State> {}
impl<A: Clone, OA, Out: Clone, Err, State> Clone for To<A, OA, Out, Err, State> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            to: self.to.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, In, Out, Err, State, Ctx, A, OA> Parser<'a, In, Out, Err, State, Ctx> for To<A, OA, Out, Err, State>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
    A: Parser<'a, In, OA, Err, State, Ctx>,
    Out: Clone,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, Out, Err> {
        self.parser
            .go::<Check>(inp)
            .map(|_| M::bind(|| self.to.clone()))
    }

    go_extra!(Out);
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

impl<'a, In, Err, State, Ctx, A, OA> Parser<'a, In, (), Err, State, Ctx> for Ignored<A, OA>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
    A: Parser<'a, In, OA, Err, State, Ctx>,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, (), Err> {
        self.parser.go::<Check>(inp).map(|_| M::bind(|| ()))
    }

    go_extra!(());
}

/// See [`Parser::then`].
pub struct Then<A, B, OA, OB, E = EmptyErr, S = ()> {
    pub(crate) parser_a: A,
    pub(crate) parser_b: B,
    pub(crate) phantom: PhantomData<(OA, OB, E, S)>,
}

impl<A: Copy, B: Copy, OA, OB, Err, State> Copy for Then<A, B, OA, OB, Err, State> {}
impl<A: Clone, B: Clone, OA, OB, Err, State> Clone for Then<A, B, OA, OB, Err, State> {
    fn clone(&self) -> Self {
        Self {
            parser_a: self.parser_a.clone(),
            parser_b: self.parser_b.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, In, Err, State, Ctx, A, B, OA, OB> Parser<'a, In, (OA, OB), Err, State, Ctx> for Then<A, B, OA, OB, Err, State>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
    A: Parser<'a, In, OA, Err, State, Ctx>,
    B: Parser<'a, In, OB, Err, State, Ctx>,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, (OA, OB), Err> {
        let a = self.parser_a.go::<M>(inp)?;
        let b = self.parser_b.go::<M>(inp)?;
        Ok(M::combine(a, b, |a: OA, b: OB| (a, b)))
    }

    go_extra!((OA, OB));
}

/// See [`Parser::ignore_then`].
pub struct IgnoreThen<A, B, OA, E = EmptyErr, S = ()> {
    pub(crate) parser_a: A,
    pub(crate) parser_b: B,
    pub(crate) phantom: PhantomData<(OA, E, S)>,
}

impl<A: Copy, B: Copy, OA, Err, State> Copy for IgnoreThen<A, B, OA, Err, State> {}
impl<A: Clone, B: Clone, OA, Err, State> Clone for IgnoreThen<A, B, OA, Err, State> {
    fn clone(&self) -> Self {
        Self {
            parser_a: self.parser_a.clone(),
            parser_b: self.parser_b.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, In, Err, State, Ctx, A, B, OA, OB> Parser<'a, In, OB, Err, State, Ctx> for IgnoreThen<A, B, OA, Err, State>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
    A: Parser<'a, In, OA, Err, State, Ctx>,
    B: Parser<'a, In, OB, Err, State, Ctx>,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, OB, Err> {
        let _a = self.parser_a.go::<Check>(inp)?;
        let b = self.parser_b.go::<M>(inp)?;
        Ok(M::map(b, |b: OB| b))
    }

    go_extra!(OB);
}

/// See [`Parser::then_ignore`].
pub struct ThenIgnore<A, B, OB, E = EmptyErr, S = ()> {
    pub(crate) parser_a: A,
    pub(crate) parser_b: B,
    pub(crate) phantom: PhantomData<(OB, E, S)>,
}

impl<A: Copy, B: Copy, OB, Err, State> Copy for ThenIgnore<A, B, OB, Err, State> {}
impl<A: Clone, B: Clone, OB, Err, State> Clone for ThenIgnore<A, B, OB, Err, State> {
    fn clone(&self) -> Self {
        Self {
            parser_a: self.parser_a.clone(),
            parser_b: self.parser_b.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, In, Err, State, Ctx, A, B, OA, OB> Parser<'a, In, OA, Err, State, Ctx> for ThenIgnore<A, B, OB, Err, State>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
    A: Parser<'a, In, OA, Err, State, Ctx>,
    B: Parser<'a, In, OB, Err, State, Ctx>,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, OA, Err> {
        let a = self.parser_a.go::<M>(inp)?;
        let _b = self.parser_b.go::<Check>(inp)?;
        Ok(M::map(a, |a: OA| a))
    }

    go_extra!(OA);
}

/// See [`Parser::then_with`].
pub struct ThenWithCtx<A, B, OA, F, In: ?Sized, Err = EmptyErr, S = (), CtxN = ()> {
    pub(crate) parser: A,
    pub(crate) then: B,
    pub(crate) make_ctx: F,
    pub(crate) phantom: PhantomData<(B, OA, Err, S, CtxN, In)>,
}

impl<A: Copy, B: Copy, OA, F: Copy, In: ?Sized, Err, State, CtxN> Copy for ThenWithCtx<A, B, OA, F, In, Err, State, CtxN> {}
impl<A: Clone, B: Clone, OA, F: Clone, In: ?Sized, Err, State, CtxN> Clone for ThenWithCtx<A, B, OA, F, In, Err, State, CtxN> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            then: self.then.clone(),
            make_ctx: self.make_ctx.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, In, Err, State, Ctx, CtxN, A, B, OA, OB, F> Parser<'a, In, OB, Err, State, Ctx> for ThenWithCtx<A, B, OA, F, In, Err, CtxN>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
    A: Parser<'a, In, OA, Err, State, Ctx>,
    B: Parser<'a, In, OB, Err, State, CtxN>,
    F: Fn(&Ctx, OA) -> CtxN,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, OB, Err> {
        let p1 = self.parser.go::<Emit>(inp)?;
        let ctx = (self.make_ctx)(inp.ctx(), p1);
        inp.with_ctx(
            ctx,
            |inp| self.then.go::<M>(inp)
        )
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

impl<'a, In, Err, State, Ctx, A, B, C, OA, OB, OC> Parser<'a, In, OA, Err, State, Ctx> for DelimitedBy<A, B, C, OB, OC>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
    A: Parser<'a, In, OA, Err, State, Ctx>,
    B: Parser<'a, In, OB, Err, State, Ctx>,
    C: Parser<'a, In, OC, Err, State, Ctx>,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, OA, Err> {
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

impl<'a, In, Err, State, Ctx, A, B, OA, OB> Parser<'a, In, OA, Err, State, Ctx> for PaddedBy<A, B, OB>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
    A: Parser<'a, In, OA, Err, State, Ctx>,
    B: Parser<'a, In, OB, Err, State, Ctx>,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, OA, Err> {
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

impl<'a, In, Out, Err, State, Ctx, A, B> Parser<'a, In, Out, Err, State, Ctx> for Or<A, B>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
    A: Parser<'a, In, Out, Err, State, Ctx>,
    B: Parser<'a, In, Out, Err, State, Ctx>,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, Out, Err> {
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

    go_extra!(Out);
}

/// See [`Parser::recover_with`].
#[derive(Copy, Clone)]
pub struct RecoverWith<A, F> {
    pub(crate) parser: A,
    pub(crate) fallback: F,
}

impl<'a, In, Out, Err, State, Ctx, A, F> Parser<'a, In, Out, Err, State, Ctx> for RecoverWith<A, F>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
    A: Parser<'a, In, Out, Err, State, Ctx>,
    F: Parser<'a, In, Out, Err, State, Ctx>,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, Out, Err> {
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

    go_extra!(Out);
}

/// See [`Parser::repeated`].
// FIXME: why C, E, S have default values?
pub struct Repeated<A, OA, In: ?Sized, C = (), E = EmptyErr, S = ()> {
    pub(crate) parser: A,
    pub(crate) at_least: usize,
    pub(crate) at_most: Option<usize>,
    pub(crate) phantom: PhantomData<(OA, C, E, S, In)>,
}

impl<A: Copy, OA, In: ?Sized, C, Err, State> Copy for Repeated<A, OA, In, C, Err, State> {}
impl<A: Clone, OA, In: ?Sized, C, Err, State> Clone for Repeated<A, OA, In, C, Err, State> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            at_least: self.at_least,
            at_most: self.at_most,
            phantom: PhantomData,
        }
    }
}

impl<'a, A, OA, In, C, Err, State> Repeated<A, OA, In, C, Err, State>
where
    A: Parser<'a, In, OA, Err, State>,
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
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
    /// let ring = just('O')
    ///     .error::<Simple<str>>()
    ///     .state::<()>();
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
    ///     rings.parse("OOOOOOOOOOOOOOOOOOO").into_result(),
    ///     Ok(((((vec!['O'; 3]), vec!['O'; 6]), vec!['O'; 9]), vec!['O'; 1])),
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
    pub fn collect<D: Container<OA>>(self) -> Repeated<A, OA, In, D, Err, State>
    where
        A: Parser<'a, In, OA, Err, State>,
    {
        Repeated {
            parser: self.parser,
            at_least: self.at_least,
            at_most: self.at_most,
            phantom: PhantomData,
        }
    }
}

impl<'a, In, Err, State, Ctx, A, OA, C> Parser<'a, In, C, Err, State, Ctx> for Repeated<A, OA, In, C, Err, State>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
    A: Parser<'a, In, OA, Err, State, Ctx>,
    C: Container<OA>,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, C, Err> {
        let mut count = 0;
        let mut output = M::bind::<C, _>(|| C::default());
        loop {
            let before = inp.save();
            match self.parser.go::<M>(inp) {
                Ok(out) => {
                    output = M::combine(output, out, |mut output: C, out| {
                        output.push(out);
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
pub struct SeparatedBy<A, B, OA, OB, In: ?Sized, C = (), Err = EmptyErr, State = ()> {
    pub(crate) parser: A,
    pub(crate) separator: B,
    pub(crate) at_least: usize,
    pub(crate) at_most: Option<usize>,
    pub(crate) allow_leading: bool,
    pub(crate) allow_trailing: bool,
    pub(crate) phantom: PhantomData<(OA, OB, C, Err, State, In)>,
}

impl<A: Copy, B: Copy, OA, OB, In: ?Sized, C, Err, State> Copy for SeparatedBy<A, B, OA, OB, In, C, Err, State> {}
impl<A: Clone, B: Clone, OA, OB, In: ?Sized, C, Err, State> Clone
    for SeparatedBy<A, B, OA, OB, In, C, Err, State>
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

impl<'a, A, B, OA, OB, In, C, Err, State> SeparatedBy<A, B, OA, OB, In, C, Err, State>
where
    A: Parser<'a, In, OA, Err, State>,
    B: Parser<'a, In, OB, Err, State>,
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
{
    /// Require that the pattern appear at least a minimum number of times.
    ///
    /// ```
    /// # use chumsky::zero_copy::prelude::*;
    /// let numbers = just('-')
    ///     .error::<Simple<str>>()
    ///     .state::<()>()
    ///     .separated_by(just('.'))
    ///     .at_least(2)
    ///     .collect::<Vec<_>>();
    ///
    /// assert!(numbers.parse("").has_errors());
    /// assert!(numbers.parse("-").has_errors());
    /// assert_eq!(numbers.parse("-.-").into_result(), Ok(vec!['-', '-']));
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
    ///     matrix_4x4.parse("0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15").into_result(),
    ///     Ok(vec![
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
    /// assert_eq!(coordinate_3d.parse("5, 0, 12").into_result(), Ok(vec!["5", "0", "12"]));
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
    /// assert_eq!(r#enum.parse("enum True | False").into_result(), Ok(vec!["True", "False"]));
    /// assert_eq!(r#enum.parse("
    ///     enum
    ///     | True
    ///     | False
    /// ").into_result(), Ok(vec!["True", "False"]));
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
    /// assert_eq!(numbers.parse("(1, 2)").into_result(), Ok(vec!["1", "2"]));
    /// assert_eq!(numbers.parse("(1, 2,)").into_result(), Ok(vec!["1", "2"]));
    /// ```
    pub fn allow_trailing(self) -> Self {
        Self {
            allow_trailing: true,
            ..self
        }
    }

    /// Set the type of [`Container`] to collect into.
    pub fn collect<D: Container<OA>>(self) -> SeparatedBy<A, B, OA, OB, In, D, Err, State>
    where
        A: Parser<'a, In, OA, Err, State>,
        B: Parser<'a, In, OB, Err, State>,
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

impl<'a, In, Err, State, Ctx, A, B, OA, OB, C> Parser<'a, In, C, Err, State, Ctx> for SeparatedBy<A, B, OA, OB, In, C, Err, State>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
    A: Parser<'a, In, OA, Err, State, Ctx>,
    B: Parser<'a, In, OB, Err, State, Ctx>,
    C: Container<OA>,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, C, Err> {
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

impl<'a, In, Out, Err, State, Ctx, A> Parser<'a, In, Option<Out>, Err, State, Ctx> for OrNot<A>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
    A: Parser<'a, In, Out, Err, State, Ctx>,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, Option<Out>, Err> {
        let before = inp.save();
        Ok(match self.parser.go::<M>(inp) {
            Ok(o) => M::map::<Out, _, _>(o, Some),
            Err(_) => {
                inp.rewind(before);
                M::bind::<Option<Out>, _>(|| None)
            }
        })
    }

    go_extra!(Option<Out>);
}

/// See [`Parser::not`].
#[derive(Copy, Clone)]
pub struct Not<A, OA> {
    pub(crate) parser: A,
    pub(crate) phantom: PhantomData<OA>,
}

impl<'a, In, Err, State, Ctx, A, OA> Parser<'a, In, (), Err, State, Ctx> for Not<A, OA>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
    A: Parser<'a, In, OA, Err, State, Ctx>,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, (), Err> {
        let before = inp.save();

        let result = self.parser.go::<Check>(inp);
        inp.rewind(before);

        match result {
            Ok(_) => {
                let (at, tok) = inp.next();
                Err(Located::at(
                    at,
                    Err::expected_found(None, tok, inp.span_since(before)),
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

impl<'a, In, Err, State, Ctx, A, B, OA, OB> Parser<'a, In, OA, Err, State, Ctx> for AndIs<A, B, OB>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
    A: Parser<'a, In, OA, Err, State, Ctx>,
    B: Parser<'a, In, OB, Err, State, Ctx>,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, OA, Err> {
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

/// See [`Parser::repeated_exactly`].
#[derive(Copy, Clone)]
pub struct RepeatedExactly<A, OA, C, const N: usize> {
    pub(crate) parser: A,
    pub(crate) phantom: PhantomData<(OA, C)>,
}

impl<A, OA, C, const N: usize> RepeatedExactly<A, OA, C, N> {
    /// Set the type of [`ContainerExactly`] to collect into.
    pub fn collect<'a, In, Err, State, D>(self) -> RepeatedExactly<A, OA, D, N>
    where
        A: Parser<'a, In, OA, Err, State>,
        In: Input + ?Sized,
        Err: Error<In>,
        State: 'a,
        D: ContainerExactly<OA, N>,
    {
        RepeatedExactly {
            parser: self.parser,
            phantom: PhantomData,
        }
    }
}

impl<'a, In, Err, State, Ctx, A, OA, C, const N: usize> Parser<'a, In, C, Err, State, Ctx> for RepeatedExactly<A, OA, C, N>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
    A: Parser<'a, In, OA, Err, State, Ctx>,
    C: ContainerExactly<OA, N>,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, C, Err> {
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
    /// assert_eq!(r#enum.parse("enum True | False").into_result(), Ok(vec!["True", "False"]));
    /// assert_eq!(r#enum.parse("
    ///     enum
    ///     | True
    ///     | False
    /// ").into_result(), Ok(vec!["True", "False"]));
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
    /// assert_eq!(numbers.parse("(1, 2)").into_result(), Ok(vec!["1", "2"]));
    /// assert_eq!(numbers.parse("(1, 2,)").into_result(), Ok(vec!["1", "2"]));
    /// ```
    pub fn allow_trailing(self) -> Self {
        Self {
            allow_trailing: true,
            ..self
        }
    }

    /// Set the type of [`ContainerExactly`] to collect into.
    pub fn collect<'a, In, OA, Err, State, D>(self) -> SeparatedByExactly<A, B, OB, D, N>
    where
        A: Parser<'a, In, OA, Err, State>,
        In: Input,
        Err: Error<In>,
        State: 'a,
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

// FIXMErr: why parser output is not C ?
impl<'a, In, Err, State, Ctx, A, B, OA, OB, C, const N: usize> Parser<'a, In, [OA; N], Err, State, Ctx>
    for SeparatedByExactly<A, B, OB, C, N>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
    A: Parser<'a, In, OA, Err, State, Ctx>,
    B: Parser<'a, In, OB, Err, State, Ctx>,
    C: ContainerExactly<OA, N>,
{
    type Config = ();

    // FIXMErr: why parse result output is not C ?
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, [OA; N], Err> {
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
pub struct Foldr<P, F, A, B, E = EmptyErr, S = ()> {
    pub(crate) parser: P,
    pub(crate) folder: F,
    pub(crate) phantom: PhantomData<(A, B, E, S)>,
}

impl<P: Copy, F: Copy, A, B, Err, State> Copy for Foldr<P, F, A, B, Err, State> {}
impl<P: Clone, F: Clone, A, B, Err, State> Clone for Foldr<P, F, A, B, Err, State> {
    fn clone(&self) -> Self {
        Foldr {
            parser: self.parser.clone(),
            folder: self.folder.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, In, P, F, A, B, Err, State, Ctx> Parser<'a, In, B, Err, State, Ctx> for Foldr<P, F, A, B, Err, State>
where
    In: Input + ?Sized,
    P: Parser<'a, In, (A, B), Err, State, Ctx>,
    Err: Error<In>,
    State: 'a,
    A: IntoIterator,
    A::IntoIter: DoubleEndedIterator,
    F: Fn(A::Item, B) -> B,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, B, Err>
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
pub struct Foldl<P, F, A, B, E = EmptyErr, S = ()> {
    pub(crate) parser: P,
    pub(crate) folder: F,
    pub(crate) phantom: PhantomData<(A, B, E, S)>,
}

impl<P: Copy, F: Copy, A, B, Err, State> Copy for Foldl<P, F, A, B, Err, State> {}
impl<P: Clone, F: Clone, A, B, Err, State> Clone for Foldl<P, F, A, B, Err, State> {
    fn clone(&self) -> Self {
        Foldl {
            parser: self.parser.clone(),
            folder: self.folder.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, In, P, F, A, B, Err, State, Ctx> Parser<'a, In, A, Err, State, Ctx> for Foldl<P, F, A, B, Err, State>
where
    In: Input + ?Sized,
    P: Parser<'a, In, (A, B), Err, State, Ctx>,
    Err: Error<In>,
    State: 'a,
    B: IntoIterator,
    F: Fn(A, B::Item) -> A,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, A, Err>
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

impl<'a, In, Out, Err, State, Ctx, A> Parser<'a, In, Out, Err, State, Ctx> for Rewind<A>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
    A: Parser<'a, In, Out, Err, State, Ctx>,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, Out, Err> {
        let before = inp.save();
        match self.parser.go::<M>(inp) {
            Ok(o) => {
                inp.rewind(before);
                Ok(o)
            }
            Err(e) => Err(e),
        }
    }

    go_extra!(Out);
}

/// See [`Parser::map_err`].
#[derive(Copy, Clone)]
pub struct MapErr<A, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
}

impl<'a, In, Out, Err, State, Ctx, A, F> Parser<'a, In, Out, Err, State, Ctx> for MapErr<A, F>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
    A: Parser<'a, In, Out, Err, State, Ctx>,
    F: Fn(Err) -> Err,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, Out, Err>
    where
        Self: Sized,
    {
        self.parser.go::<M>(inp).map_err(|mut e| {
            e.err = (self.mapper)(e.err);
            e
        })
    }

    go_extra!(Out);
}

/// See [`Parser::map_err_with_span`].
#[derive(Copy, Clone)]
pub struct MapErrWithSpan<A, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
}

impl<'a, In, Out, Err, State, Ctx, A, F> Parser<'a, In, Out, Err, State, Ctx> for MapErrWithSpan<A, F>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
    A: Parser<'a, In, Out, Err, State, Ctx>,
    F: Fn(Err, In::Span) -> Err,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, Out, Err>
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

    go_extra!(Out);
}

/// See [`Parser::map_err_with_state`].
#[derive(Copy, Clone)]
pub struct MapErrWithState<A, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
}

impl<'a, In, Out, Err, State, Ctx, A, F> Parser<'a, In, Out, Err, State, Ctx> for MapErrWithState<A, F>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
    A: Parser<'a, In, Out, Err, State, Ctx>,
    F: Fn(Err, In::Span, &mut State) -> Err,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, Out, Err>
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

    go_extra!(Out);
}

/// See [`Parser::validate`]
pub struct Validate<A, OA, F> {
    pub(crate) parser: A,
    pub(crate) validator: F,
    pub(crate) phantom: PhantomData<OA>,
}

impl<A: Copy, OA, F: Copy> Copy for Validate<A, OA, F> {}
impl<A: Clone, OA, F: Clone> Clone for Validate<A, OA, F> {
    fn clone(&self) -> Self {
        Validate {
            parser: self.parser.clone(),
            validator: self.validator.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, In, OA, U, Err, State, Ctx, A, F> Parser<'a, In, U, Err, State, Ctx> for Validate<A, OA, F>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
    A: Parser<'a, In, OA, Err, State, Ctx>,
    F: Fn(OA, In::Span, &mut Emitter<Err>) -> U,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, U, Err>
    where
        Self: Sized,
    {
        let before = inp.save();
        self.parser.go::<Emit>(inp).map(|out| {
            let span = inp.span_since(before);
            let mut emitter = Emitter::new();
            let out = (self.validator)(out, span, &mut emitter);
            for err in emitter.errors() {
                inp.emit(err);
            }
            M::bind(|| out)
        })
    }

    go_extra!(U);
}

/// See [`Parser::or_else`].
#[derive(Copy, Clone)]
pub struct OrElse<A, F> {
    pub(crate) parser: A,
    pub(crate) or_else: F,
}

impl<'a, In, Out, Err, State, Ctx, A, F> Parser<'a, In, Out, Err, State, Ctx> for OrElse<A, F>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
    A: Parser<'a, In, Out, Err, State, Ctx>,
    F: Fn(Err) -> Result<Out, Err>,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, Out, Err>
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

    go_extra!(Out);
}

#[cfg(test)]
mod tests {
    use crate::zero_copy::prelude::*;

    #[test]
    fn separated_by_at_least() {
        let parser = just('-')
            .error::<EmptyErr>()
            .separated_by(just(','))
            .at_least(3)
            .collect();

        assert_eq!(parser.parse("-,-,-").into_result(), Ok(vec!['-', '-', '-']));
    }

    #[test]
    fn separated_by_at_least_without_leading() {
        let parser = just('-')
            .error::<EmptyErr>()
            .separated_by(just(','))
            .at_least(3)
            .collect::<Vec<_>>();

        // Is empty means no errors
        assert!(parser.parse(",-,-,-").has_errors());
    }

    #[test]
    fn separated_by_at_least_without_trailing() {
        let parser = just('-')
            .error::<EmptyErr>()
            .separated_by(just(','))
            .at_least(3)
            .collect::<Vec<_>>()
            .then(end());

        // Is empty means no errors
        assert!(parser.parse("-,-,-,").has_errors());
    }

    #[test]
    fn separated_by_at_least_with_leading() {
        let parser = just('-')
            .error::<EmptyErr>()
            .separated_by(just(','))
            .allow_leading()
            .at_least(3)
            .collect();

        assert_eq!(parser.parse(",-,-,-").into_result(), Ok(vec!['-', '-', '-']));
        assert!(parser.parse(",-,-").has_errors());
    }

    #[test]
    fn separated_by_at_least_with_trailing() {
        let parser = just('-')
            .error::<EmptyErr>()
            .separated_by(just(','))
            .allow_trailing()
            .at_least(3)
            .collect();

        assert_eq!(parser.parse("-,-,-,").into_result(), Ok(vec!['-', '-', '-']));
        assert!(parser.parse("-,-,").has_errors());
    }

    #[test]
    fn separated_by_leaves_last_separator() {
        let parser = just('-')
            .error::<EmptyErr>()
            .separated_by(just(','))
            .collect::<Vec<_>>()
            .chain(just(','));
        assert_eq!(
            parser.parse("-,-,-,").into_result(),
            Ok(vec!['-', '-', '-', ',']),
        )
    }
}
