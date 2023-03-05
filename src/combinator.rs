//! Combinators that allow combining and extending existing parsers.
//!
//! *“Ford... you're turning into a penguin. Stop it.”*
//!
//! Although it's *sometimes* useful to be able to name their type, most of these parsers are much easier to work with
//! when accessed through their respective methods on [`Parser`].

use super::*;
use core::mem::MaybeUninit;

/// The type of a lazy parser.
pub type Lazy<'a, A, I, E> =
    ThenIgnore<A, Repeated<Any<I, E>, <I as Input<'a>>::Token, I, E>, (), E>;

/// Alter the configuration of a struct using parse-time context
pub struct Configure<A, F> {
    pub(crate) parser: A,
    pub(crate) cfg: F,
}

impl<A: Copy, F: Copy> Copy for Configure<A, F> {}
impl<A: Clone, F: Clone> Clone for Configure<A, F> {
    fn clone(&self) -> Self {
        Configure {
            parser: self.parser.clone(),
            cfg: self.cfg.clone(),
        }
    }
}

impl<'a, I, O, E, A, F> Parser<'a, I, O, E> for Configure<A, F>
where
    A: ConfigParser<'a, I, O, E>,
    F: Fn(A::Config, &E::Context) -> A::Config,
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O>
    where
        Self: Sized,
    {
        let cfg = (self.cfg)(A::Config::default(), inp.ctx());
        self.parser.go_cfg::<M>(inp, cfg)
    }

    go_extra!(O);
}

/// See [`ConfigIterParser::configure`]
pub struct IterConfigure<A, F, OA> {
    pub(crate) parser: A,
    pub(crate) cfg: F,
    pub(crate) phantom: PhantomData<OA>,
}

impl<A: Copy, F: Copy, OA> Copy for IterConfigure<A, F, OA> {}
impl<A: Clone, F: Clone, OA> Clone for IterConfigure<A, F, OA> {
    fn clone(&self) -> Self {
        IterConfigure {
            parser: self.parser.clone(),
            cfg: self.cfg.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, OA, E, A, F> Parser<'a, I, (), E> for IterConfigure<A, F, OA>
where
    A: ConfigIterParser<'a, I, OA, E>,
    F: Fn(A::Config, &E::Context) -> A::Config,
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, ()> {
        let mut state = self.make_iter::<Check>(inp)?;
        loop {
            match self.next::<Check>(inp, &mut state) {
                Ok(Some(())) => {}
                Ok(None) => break Ok(M::bind(|| ())),
                Err(()) => break Err(()),
            }
        }
    }

    go_extra!(());
}

impl<'a, I, O, E, A, F> IterParser<'a, I, O, E> for IterConfigure<A, F, O>
where
    A: ConfigIterParser<'a, I, O, E>,
    F: Fn(A::Config, &E::Context) -> A::Config,
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    type IterState<M: Mode> = (A::IterState<M>, A::Config)
    where
        I: 'a;

    fn make_iter<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
    ) -> PResult<Emit, Self::IterState<M>> {
        Ok((
            A::make_iter(&self.parser, inp)?,
            (self.cfg)(A::Config::default(), inp.ctx()),
        ))
    }

    fn next<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        state: &mut Self::IterState<M>,
    ) -> IPResult<M, O> {
        self.parser.next_cfg(inp, &mut state.0, &state.1)
    }
}

/// See [`Parser::map_slice`].
pub struct MapSlice<'a, A, I, O, E, F, U>
where
    I: SliceInput<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, O, E>,
    F: Fn(I::Slice) -> U,
{
    pub(crate) parser: A,
    pub(crate) mapper: F,
    pub(crate) phantom: PhantomData<(I::Slice, O, E)>,
}

impl<'a, A: Copy, I, O, E, F: Copy, U> Copy for MapSlice<'a, A, I, O, E, F, U>
where
    I: SliceInput<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, O, E>,
    F: Fn(I::Slice) -> U,
{
}
impl<'a, A: Clone, I, O, E, F: Clone, U> Clone for MapSlice<'a, A, I, O, E, F, U>
where
    I: Input<'a> + SliceInput<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, O, E>,
    F: Fn(I::Slice) -> U,
{
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            mapper: self.mapper.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, O, E, A, F, U> Parser<'a, I, U, E> for MapSlice<'a, A, I, O, E, F, U>
where
    I: SliceInput<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, O, E>,
    F: Fn(I::Slice) -> U,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, U> {
        let before = inp.offset();
        self.parser.go::<Check>(inp)?;
        let after = inp.offset();

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

impl<'a, A, I, O, E> Parser<'a, I, I::Slice, E> for Slice<A, O>
where
    A: Parser<'a, I, O, E>,
    I: SliceInput<'a>,
    E: ParserExtra<'a, I>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, I::Slice>
    where
        Self: Sized,
    {
        let before = inp.offset();
        self.parser.go::<Check>(inp)?;
        let after = inp.offset();

        Ok(M::bind(|| inp.slice(before..after)))
    }

    go_extra!(I::Slice);
}

/// See [`Parser::filter`].
pub struct Filter<A, F> {
    pub(crate) parser: A,
    pub(crate) filter: F,
}

impl<A: Copy, F: Copy> Copy for Filter<A, F> {}
impl<A: Clone, F: Clone> Clone for Filter<A, F> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            filter: self.filter.clone(),
        }
    }
}

impl<'a, A, I, O, E, F> Parser<'a, I, O, E> for Filter<A, F>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, O, E>,
    F: Fn(&O) -> bool,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        let before = inp.offset();
        self.parser.go::<Emit>(inp).and_then(|out| {
            if (self.filter)(&out) {
                Ok(M::bind(|| out))
            } else {
                // SAFETY: Using offsets derived from input
                let span = unsafe { inp.span_since(before) };
                inp.add_alt(Located::at(
                    inp.offset().into(),
                    E::Error::expected_found(None, None, span),
                ));
                Err(())
            }
        })
    }

    go_extra!(O);
}

/// See [`Parser::map`].
pub struct Map<A, OA, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
    pub(crate) phantom: PhantomData<OA>,
}

impl<A: Copy, OA, F: Copy> Copy for Map<A, OA, F> {}
impl<A: Clone, OA, F: Clone> Clone for Map<A, OA, F> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            mapper: self.mapper.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, O, E, A, OA, F> Parser<'a, I, O, E> for Map<A, OA, F>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
    F: Fn(OA) -> O,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        let out = self.parser.go::<M>(inp)?;
        Ok(M::map(out, &self.mapper))
    }

    go_extra!(O);
}

impl<'a, I, O, E, A, OA, F> IterParser<'a, I, O, E> for Map<A, OA, F>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: IterParser<'a, I, OA, E>,
    F: Fn(OA) -> O,
{
    type IterState<M: Mode> = A::IterState<M>
    where
        I: 'a;

    fn make_iter<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
    ) -> PResult<Emit, Self::IterState<M>> {
        self.parser.make_iter(inp)
    }

    fn next<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        state: &mut Self::IterState<M>,
    ) -> IPResult<M, O> {
        match self.parser.next::<M>(inp, state) {
            Ok(Some(o)) => Ok(Some(M::map(o, |o| (self.mapper)(o)))),
            Ok(None) => Ok(None),
            Err(()) => Err(()),
        }
    }
}

/// See [`Parser::map_with_span`].
pub struct MapWithSpan<A, OA, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
    pub(crate) phantom: PhantomData<OA>,
}

impl<A: Copy, OA, F: Copy> Copy for MapWithSpan<A, OA, F> {}
impl<A: Clone, OA, F: Clone> Clone for MapWithSpan<A, OA, F> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            mapper: self.mapper.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, O, E, A, OA, F> Parser<'a, I, O, E> for MapWithSpan<A, OA, F>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
    F: Fn(OA, I::Span) -> O,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        let before = inp.offset();
        let out = self.parser.go::<M>(inp)?;
        Ok(M::map(out, |out| {
            // SAFETY: Using offsets derived from input
            let span = unsafe { inp.span_since(before) };
            (self.mapper)(out, span)
        }))
    }

    go_extra!(O);
}

/// See [`Parser::map_with_state`].
pub struct MapWithState<A, OA, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
    pub(crate) phantom: PhantomData<OA>,
}

impl<A: Copy, OA, F: Copy> Copy for MapWithState<A, OA, F> {}
impl<A: Clone, OA, F: Clone> Clone for MapWithState<A, OA, F> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            mapper: self.mapper.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, O, E, A, OA, F> Parser<'a, I, O, E> for MapWithState<A, OA, F>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
    F: Fn(OA, I::Span, &mut E::State) -> O,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        let before = inp.offset();
        let out = self.parser.go::<Emit>(inp)?;
        Ok(M::bind(|| {
            // SAFETY: Using offsets derived from input
            let span = unsafe { inp.span_since(before) };
            let state = inp.state();
            (self.mapper)(out, span, state)
        }))
    }

    go_extra!(O);
}

/// See [`Parser::try_map`].
pub struct TryMap<A, OA, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
    pub(crate) phantom: PhantomData<OA>,
}

impl<A: Copy, OA, F: Copy> Copy for TryMap<A, OA, F> {}
impl<A: Clone, OA, F: Clone> Clone for TryMap<A, OA, F> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            mapper: self.mapper.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, O, E, A, OA, F> Parser<'a, I, O, E> for TryMap<A, OA, F>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
    F: Fn(OA, I::Span) -> Result<O, E::Error>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        let before = inp.offset();
        let out = self.parser.go::<Emit>(inp)?;
        // SAFETY: Using offsets derived from input
        let span = unsafe { inp.span_since(before) };
        match (self.mapper)(out, span) {
            Ok(out) => Ok(M::bind(|| out)),
            Err(e) => {
                inp.add_alt(Located::at(inp.offset().into(), e));
                Err(())
            }
        }
    }

    go_extra!(O);
}

/// See [`Parser::try_map_with_state`].
pub struct TryMapWithState<A, OA, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
    pub(crate) phantom: PhantomData<OA>,
}

impl<A: Copy, OA, F: Copy> Copy for TryMapWithState<A, OA, F> {}
impl<A: Clone, OA, F: Clone> Clone for TryMapWithState<A, OA, F> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            mapper: self.mapper.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, O, E, A, OA, F> Parser<'a, I, O, E> for TryMapWithState<A, OA, F>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
    F: Fn(OA, I::Span, &mut E::State) -> Result<O, E::Error>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        let before = inp.offset();
        let out = self.parser.go::<Emit>(inp)?;
        // SAFETY: Using offsets derived from input
        let span = unsafe { inp.span_since(before) };
        match (self.mapper)(out, span, inp.state()) {
            Ok(out) => Ok(M::bind(|| out)),
            Err(e) => {
                inp.add_alt(Located::at(inp.offset().into(), e));
                Err(())
            }
        }
    }

    go_extra!(O);
}

/// See [`Parser::to`].
pub struct To<A, OA, O> {
    pub(crate) parser: A,
    pub(crate) to: O,
    pub(crate) phantom: PhantomData<OA>,
}

impl<A: Copy, OA, O: Copy> Copy for To<A, OA, O> {}
impl<A: Clone, OA, O: Clone> Clone for To<A, OA, O> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            to: self.to.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, O, E, A, OA> Parser<'a, I, O, E> for To<A, OA, O>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
    O: Clone,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        let () = self.parser.go::<Check>(inp)?;
        Ok(M::bind(|| self.to.clone()))
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
        Self {
            parser: self.parser.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, A, OA> Parser<'a, I, (), E> for Ignored<A, OA>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, ()> {
        let () = self.parser.go::<Check>(inp)?;
        Ok(M::bind(|| ()))
    }

    go_extra!(());
}

/// See [`Parser::unwrapped`].
pub struct Unwrapped<A, O> {
    pub(crate) parser: A,
    pub(crate) location: Location<'static>,
    pub(crate) phantom: PhantomData<O>,
}

impl<A: Copy, O> Copy for Unwrapped<A, O> {}
impl<A: Clone, O> Clone for Unwrapped<A, O> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            location: self.location,
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, A, O, U> Parser<'a, I, O, E> for Unwrapped<A, Result<O, U>>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, Result<O, U>, E>,
    U: fmt::Debug,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        let out = self.parser.go::<M>(inp)?;
        Ok(M::map(out, |out| match out {
            Ok(out) => out,
            Err(err) => panic!(
                "called `Result::unwrap` on a `Err(_)` value at {}: {:?}",
                self.location, err
            ),
        }))
    }

    go_extra!(O);
}

impl<'a, I, E, A, O> Parser<'a, I, O, E> for Unwrapped<A, Option<O>>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, Option<O>, E>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        let out = self.parser.go::<M>(inp)?;
        Ok(M::map(out, |out| match out {
            Some(out) => out,
            None => panic!(
                "called `Option::unwrap` on a `None` value at {}",
                self.location
            ),
        }))
    }

    go_extra!(O);
}

/// See [`Parser::memoised`].
#[cfg(feature = "memoization")]
#[derive(Copy, Clone)]
pub struct Memoised<A> {
    pub(crate) parser: A,
}

#[cfg(feature = "memoization")]
impl<'a, I, E, A, O> Parser<'a, I, O, E> for Memoised<A>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    E::Error: Clone,
    A: Parser<'a, I, O, E>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        // TODO: Don't use address, since this might not be constant?
        let key = (inp.offset(), &self.parser as *const _ as *const () as usize);

        match inp.memos.entry(key) {
            hashbrown::hash_map::Entry::Occupied(o) => {
                if let Some(err) = o.get() {
                    let err = err.clone();
                    inp.add_alt(err);
                } else {
                    inp.add_alt(Located::at(
                        key.0.into(),
                        // SAFETY: Using offsets derived from input
                        Error::expected_found(None, None, unsafe { inp.span_since(key.0) }),
                    ));
                }
                return Err(());
            }
            hashbrown::hash_map::Entry::Vacant(v) => {
                v.insert(None);
            }
        }

        let res = self.parser.go::<M>(inp);

        if res.is_err() {
            inp.memos.insert(
                key,
                Some(inp.errors.alt.clone().expect("failure but no alt?!")),
            );
        } else {
            inp.memos.remove(&key);
        }

        res
    }

    go_extra!(O);
}

/// See [`Parser::then`].
pub struct Then<A, B, OA, OB, E> {
    pub(crate) parser_a: A,
    pub(crate) parser_b: B,
    pub(crate) phantom: PhantomData<(OA, OB, E)>,
}

impl<A: Copy, B: Copy, OA, OB, E> Copy for Then<A, B, OA, OB, E> {}
impl<A: Clone, B: Clone, OA, OB, E> Clone for Then<A, B, OA, OB, E> {
    fn clone(&self) -> Self {
        Self {
            parser_a: self.parser_a.clone(),
            parser_b: self.parser_b.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, A, B, OA, OB> Parser<'a, I, (OA, OB), E> for Then<A, B, OA, OB, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
    B: Parser<'a, I, OB, E>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, (OA, OB)> {
        let a = self.parser_a.go::<M>(inp)?;
        let b = self.parser_b.go::<M>(inp)?;
        Ok(M::combine(a, b, |a: OA, b: OB| (a, b)))
    }

    go_extra!((OA, OB));
}

/// See [`Parser::ignore_then`].
pub struct IgnoreThen<A, B, OA, E> {
    pub(crate) parser_a: A,
    pub(crate) parser_b: B,
    pub(crate) phantom: PhantomData<(OA, E)>,
}

impl<A: Copy, B: Copy, OA, E> Copy for IgnoreThen<A, B, OA, E> {}
impl<A: Clone, B: Clone, OA, E> Clone for IgnoreThen<A, B, OA, E> {
    fn clone(&self) -> Self {
        Self {
            parser_a: self.parser_a.clone(),
            parser_b: self.parser_b.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, A, B, OA, OB> Parser<'a, I, OB, E> for IgnoreThen<A, B, OA, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
    B: Parser<'a, I, OB, E>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, OB> {
        let _a = self.parser_a.go::<Check>(inp)?;
        let b = self.parser_b.go::<M>(inp)?;
        Ok(M::map(b, |b: OB| b))
    }

    go_extra!(OB);
}

/// See [`Parser::then_ignore`].
pub struct ThenIgnore<A, B, OB, E> {
    pub(crate) parser_a: A,
    pub(crate) parser_b: B,
    pub(crate) phantom: PhantomData<(OB, E)>,
}

impl<A: Copy, B: Copy, OB, E> Copy for ThenIgnore<A, B, OB, E> {}
impl<A: Clone, B: Clone, OB, E> Clone for ThenIgnore<A, B, OB, E> {
    fn clone(&self) -> Self {
        Self {
            parser_a: self.parser_a.clone(),
            parser_b: self.parser_b.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, A, B, OA, OB> Parser<'a, I, OA, E> for ThenIgnore<A, B, OB, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
    B: Parser<'a, I, OB, E>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, OA> {
        let a = self.parser_a.go::<M>(inp)?;
        let _b = self.parser_b.go::<Check>(inp)?;
        Ok(M::map(a, |a: OA| a))
    }

    go_extra!(OA);
}

/// See [`Parser::nested_in`].
pub struct NestedIn<A, B, O, E> {
    pub(crate) parser_a: A,
    pub(crate) parser_b: B,
    pub(crate) phantom: PhantomData<(O, E)>,
}

impl<A: Copy, B: Copy, O, E> Copy for NestedIn<A, B, O, E> {}
impl<A: Clone, B: Clone, O, E> Clone for NestedIn<A, B, O, E> {
    fn clone(&self) -> Self {
        Self {
            parser_a: self.parser_a.clone(),
            parser_b: self.parser_b.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, A, B, O> Parser<'a, I, O, E> for NestedIn<A, B, O, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, O, E>,
    B: Parser<'a, I, I, E>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        let inp2 = self.parser_b.go::<Emit>(inp)?;

        let alt = inp.errors.alt.take();

        let res = inp.with_input(&inp2, |inp| self.then_ignore(end()).parser_a.go::<M>(inp));

        // TODO: Translate secondary error offsets too
        let new_alt = inp
            .errors
            .alt
            .take()
            .map(|err| Located::at(inp.offset().into(), err.err));
        inp.errors.alt = alt;
        if let Some(new_alt) = new_alt {
            inp.add_alt(new_alt);
        }

        res
    }

    go_extra!(O);
}

/// See [`Parser::then_with_ctx`].
pub struct ThenWithCtx<A, B, OA, I: ?Sized, E> {
    pub(crate) parser: A,
    pub(crate) then: B,
    pub(crate) phantom: PhantomData<(B, OA, E, I)>,
}

impl<A: Copy, B: Copy, OA, I: ?Sized, E> Copy for ThenWithCtx<A, B, OA, I, E> {}
impl<A: Clone, B: Clone, OA, I: ?Sized, E> Clone for ThenWithCtx<A, B, OA, I, E> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            then: self.then.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, A, B, OA, OB> Parser<'a, I, OB, E>
    for ThenWithCtx<A, B, OA, I, extra::Full<E::Error, E::State, OA>>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
    B: Parser<'a, I, OB, extra::Full<E::Error, E::State, OA>>,
    OA: 'a,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, OB> {
        let p1 = self.parser.go::<Emit>(inp)?;
        inp.with_ctx(&p1, |inp| self.then.go::<M>(inp))
    }

    go_extra!(OB);
}

impl<'a, I, E, A, B, OA, OB> IterParser<'a, I, OB, E>
    for ThenWithCtx<A, B, OA, I, extra::Full<E::Error, E::State, OA>>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
    B: IterParser<'a, I, OB, extra::Full<E::Error, E::State, OA>>,
    OA: 'a,
{
    type IterState<M: Mode> = (OA, B::IterState<M>)
    where
        I: 'a;

    fn make_iter<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
    ) -> PResult<Emit, Self::IterState<M>> {
        let out = self.parser.go::<Emit>(inp)?;
        let then = inp.with_ctx(&out, |inp| self.then.make_iter::<M>(inp))?;
        Ok((out, then))
    }

    fn next<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        state: &mut Self::IterState<M>,
    ) -> IPResult<M, OB> {
        let (ctx, inner_state) = state;

        inp.with_ctx(ctx, |inp| self.then.next(inp, inner_state))
    }
}

/// See [`Parser::with_ctx`].
pub struct WithCtx<A, Ctx> {
    pub(crate) parser: A,
    pub(crate) ctx: Ctx,
}

impl<A: Copy, Ctx: Copy> Copy for WithCtx<A, Ctx> {}
impl<A: Clone, Ctx: Clone> Clone for WithCtx<A, Ctx> {
    fn clone(&self) -> Self {
        WithCtx {
            parser: self.parser.clone(),
            ctx: self.ctx.clone(),
        }
    }
}

impl<'a, I, O, E, A, Ctx> Parser<'a, I, O, E> for WithCtx<A, Ctx>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, O, extra::Full<E::Error, E::State, Ctx>>,
    Ctx: 'a,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        inp.with_ctx(&self.ctx, |inp| self.parser.go::<M>(inp))
    }

    go_extra!(O);
}

/// See [`Parser::delimited_by`].
pub struct DelimitedBy<A, B, C, OB, OC> {
    pub(crate) parser: A,
    pub(crate) start: B,
    pub(crate) end: C,
    pub(crate) phantom: PhantomData<(OB, OC)>,
}

impl<A: Copy, B: Copy, C: Copy, OB, OC> Copy for DelimitedBy<A, B, C, OB, OC> {}
impl<A: Clone, B: Clone, C: Clone, OB, OC> Clone for DelimitedBy<A, B, C, OB, OC> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            start: self.start.clone(),
            end: self.end.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, A, B, C, OA, OB, OC> Parser<'a, I, OA, E> for DelimitedBy<A, B, C, OB, OC>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
    B: Parser<'a, I, OB, E>,
    C: Parser<'a, I, OC, E>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, OA> {
        let _ = self.start.go::<Check>(inp)?;
        let a = self.parser.go::<M>(inp)?;
        let _ = self.end.go::<Check>(inp)?;
        Ok(a)
    }

    go_extra!(OA);
}

/// See [`Parser::padded_by`].
pub struct PaddedBy<A, B, OB> {
    pub(crate) parser: A,
    pub(crate) padding: B,
    pub(crate) phantom: PhantomData<OB>,
}

impl<A: Copy, B: Copy, OB> Copy for PaddedBy<A, B, OB> {}
impl<A: Clone, B: Clone, OB> Clone for PaddedBy<A, B, OB> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            padding: self.padding.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, A, B, OA, OB> Parser<'a, I, OA, E> for PaddedBy<A, B, OB>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
    B: Parser<'a, I, OB, E>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, OA> {
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
    pub(crate) choice: crate::primitive::Choice<(A, B)>,
}

impl<'a, I, O, E, A, B> Parser<'a, I, O, E> for Or<A, B>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, O, E>,
    B: Parser<'a, I, O, E>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        self.choice.go::<M>(inp)
    }

    go_extra!(O);
}

/// Configuration for [`Parser::repeated`], used in [`ConfigParser::configure`].
#[derive(Default)]
pub struct RepeatedCfg {
    at_least: Option<usize>,
    at_most: Option<usize>,
}

impl RepeatedCfg {
    /// Set the minimum number of repetitions accepted
    pub fn at_least(mut self, n: usize) -> Self {
        self.at_least = Some(n);
        self
    }

    /// Set the maximum number of repetitions accepted
    pub fn at_most(mut self, n: usize) -> Self {
        self.at_most = Some(n);
        self
    }

    /// Set an exact number of repetitions to accept
    pub fn exactly(mut self, n: usize) -> Self {
        self.at_least = Some(n);
        self.at_most = Some(n);
        self
    }
}

/// See [`Parser::repeated`].
pub struct Repeated<A, OA, I: ?Sized, E> {
    pub(crate) parser: A,
    pub(crate) at_least: usize,
    // Slightly evil: Should be `Option<usize>`, but we encode `!0` as 'no cap' because it's so large
    pub(crate) at_most: u64,
    pub(crate) phantom: PhantomData<(OA, E, I)>,
}

impl<A: Copy, OA, I: ?Sized, E> Copy for Repeated<A, OA, I, E> {}
impl<A: Clone, OA, I: ?Sized, E> Clone for Repeated<A, OA, I, E> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            at_least: self.at_least,
            at_most: self.at_most,
            phantom: PhantomData,
        }
    }
}

impl<'a, A, OA, I, E> Repeated<A, OA, I, E>
where
    A: Parser<'a, I, OA, E>,
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    /// Require that the pattern appear at least a minimum number of times.
    pub fn at_least(self, at_least: usize) -> Self {
        Self { at_least, ..self }
    }

    /// Require that the pattern appear at most a maximum number of times.
    pub fn at_most(self, at_most: usize) -> Self {
        Self {
            at_most: at_most as u64,
            ..self
        }
    }

    /// Require that the pattern appear exactly the given number of times. If the value provided
    /// is constant, consider instead using [`Parser::repeated_exactly`]
    ///
    /// ```
    /// # use chumsky::prelude::*;
    /// let ring = just::<_, _, extra::Err<Simple<char>>>('O');
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
    ///     .then(for_sauron);
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
            at_most: exactly as u64,
            ..self
        }
    }
}

impl<'a, I, E, A, OA> Parser<'a, I, (), E> for Repeated<A, OA, I, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, ()> {
        let mut state = self.make_iter::<Check>(inp)?;
        loop {
            match self.next::<Check>(inp, &mut state) {
                Ok(Some(())) => {}
                Ok(None) => break Ok(M::bind(|| ())),
                Err(()) => break Err(()),
            }
        }
    }

    go_extra!(());
}

impl<'a, A, O, I, E> IterParser<'a, I, O, E> for Repeated<A, O, I, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, O, E>,
{
    type IterState<M: Mode> = usize;

    fn make_iter<M: Mode>(
        &self,
        _inp: &mut InputRef<'a, '_, I, E>,
    ) -> PResult<Emit, Self::IterState<M>> {
        Ok(0)
    }

    fn next<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        count: &mut Self::IterState<M>,
    ) -> IPResult<M, O> {
        if *count as u64 >= self.at_most {
            return Ok(None);
        }

        let before = inp.save();
        match self.parser.go::<M>(inp) {
            Ok(item) => {
                *count += 1;
                Ok(Some(item))
            }
            Err(()) => {
                inp.rewind(before);
                if *count >= self.at_least {
                    Ok(None)
                } else {
                    Err(())
                }
            }
        }
    }
}

impl<'a, A, O, I, E> ConfigIterParser<'a, I, O, E> for Repeated<A, O, I, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, O, E>,
{
    type Config = RepeatedCfg;

    fn next_cfg<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        count: &mut Self::IterState<M>,
        cfg: &Self::Config,
    ) -> IPResult<M, O> {
        let at_most = cfg.at_most.map(|x| x as u64).unwrap_or(self.at_most);
        let at_least = cfg.at_least.unwrap_or(self.at_least);

        if *count as u64 >= at_most {
            return Ok(None);
        }

        let before = inp.save();
        match self.parser.go::<M>(inp) {
            Ok(item) => {
                *count += 1;
                Ok(Some(item))
            }
            Err(()) => {
                inp.rewind(before);
                if *count >= at_least {
                    Ok(None)
                } else {
                    Err(())
                }
            }
        }
    }
}

/// See [`Parser::separated_by`].
pub struct SeparatedBy<A, B, OA, OB, I: ?Sized, E> {
    pub(crate) parser: A,
    pub(crate) separator: B,
    pub(crate) at_least: usize,
    // Slightly evil: Should be `Option<usize>`, but we encode `!0` as 'no cap' because it's so large
    pub(crate) at_most: u64,
    pub(crate) allow_leading: bool,
    pub(crate) allow_trailing: bool,
    pub(crate) phantom: PhantomData<(OA, OB, E, I)>,
}

impl<A: Copy, B: Copy, OA, OB, I: ?Sized, E> Copy for SeparatedBy<A, B, OA, OB, I, E> {}
impl<A: Clone, B: Clone, OA, OB, I: ?Sized, E> Clone for SeparatedBy<A, B, OA, OB, I, E> {
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

impl<'a, A, B, OA, OB, I, E> SeparatedBy<A, B, OA, OB, I, E>
where
    A: Parser<'a, I, OA, E>,
    B: Parser<'a, I, OB, E>,
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    /// Require that the pattern appear at least a minimum number of times.
    ///
    /// ```
    /// # use chumsky::prelude::*;
    /// let numbers = just::<_, _, extra::Err<Simple<char>>>('-')
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
    /// # use chumsky::prelude::*;
    /// let row_4 = text::int::<_, _, extra::Err<Simple<char>>>(10)
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
            at_most: at_most as u64,
            ..self
        }
    }

    /// Require that the pattern appear exactly the given number of times. If the value provided is
    /// constant, consider instead using [`Parser::separated_by_exactly`].
    ///
    /// ```
    /// # use chumsky::prelude::*;
    /// let coordinate_3d = text::int::<_, _, extra::Err<Simple<char>>>(10)
    ///     .padded()
    ///     .separated_by(just(','))
    ///     .exactly(3)
    ///     .collect::<Vec<_>>();
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
            at_most: exactly as u64,
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
    /// # use chumsky::prelude::*;
    /// let r#enum = text::keyword::<_, _, _, extra::Err<Simple<char>>>("enum")
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
    /// # use chumsky::prelude::*;
    /// let numbers = text::int::<_, _, extra::Err<Simple<char>>>(10)
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
}

impl<'a, I, E, A, B, OA, OB> IterParser<'a, I, OA, E> for SeparatedBy<A, B, OA, OB, I, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
    B: Parser<'a, I, OB, E>,
{
    type IterState<M: Mode> = usize
    where
        I: 'a;

    fn make_iter<M: Mode>(
        &self,
        _inp: &mut InputRef<'a, '_, I, E>,
    ) -> PResult<Emit, Self::IterState<M>> {
        Ok(0)
    }

    fn next<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        state: &mut Self::IterState<M>,
    ) -> IPResult<M, OA> {
        if *state as u64 >= self.at_most {
            return Ok(None);
        }

        let before_separator = inp.save();
        if *state == 0 && self.allow_leading {
            if let Err(_) = self.separator.go::<Check>(inp) {
                inp.rewind(before_separator);
            }
        } else if *state > 0 {
            match self.separator.go::<Check>(inp) {
                Ok(()) => {
                    // Do nothing
                }
                Err(()) if *state < self.at_least => {
                    inp.rewind(before_separator);
                    return Err(());
                }
                Err(()) => {
                    inp.rewind(before_separator);
                    return Ok(None);
                }
            }
        }

        let before_item = inp.save();
        match self.parser.go::<M>(inp) {
            Ok(item) => {
                *state += 1;
                Ok(Some(item))
            }
            Err(()) if *state < self.at_least => {
                // We have errored before we have reached the count,
                // and therefore should return this error, as we are
                // still expecting items
                inp.rewind(before_separator);
                Err(())
            }
            Err(()) => {
                // We are not expecting any more items, so it is okay
                // for it to fail.

                // though if we don't allow trailing, we shouldn't have
                // consumed the separator, so we need to rewind it.
                if self.allow_trailing {
                    inp.rewind(before_item);
                } else {
                    inp.rewind(before_separator);
                }
                Ok(None)
            }
        }
    }
}

impl<'a, I, E, A, B, OA, OB> Parser<'a, I, (), E> for SeparatedBy<A, B, OA, OB, I, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
    B: Parser<'a, I, OB, E>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, ()> {
        let mut state = self.make_iter::<Check>(inp)?;
        loop {
            match self.next::<Check>(inp, &mut state) {
                Ok(Some(())) => {}
                Ok(None) => break Ok(M::bind(|| ())),
                Err(()) => break Err(()),
            }
        }
    }

    go_extra!(());
}

/// See [`IterParser::collect`].
pub struct Collect<A, O, C> {
    pub(crate) parser: A,
    pub(crate) phantom: PhantomData<(O, C)>,
}

impl<A: Copy, O, C> Copy for Collect<A, O, C> {}
impl<A: Clone, O, C> Clone for Collect<A, O, C> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, O, E, A, C> Parser<'a, I, C, E> for Collect<A, O, C>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: IterParser<'a, I, O, E>,
    C: Container<O>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, C> {
        let mut output = M::bind::<C, _>(|| C::default());
        let mut iter_state = self.parser.make_iter::<M>(inp)?;
        loop {
            match self.parser.next::<M>(inp, &mut iter_state) {
                Ok(Some(out)) => {
                    output = M::combine(output, out, |mut output: C, item| {
                        output.push(item);
                        output
                    });
                }
                Ok(None) => break Ok(output),
                Err(()) => break Err(()),
            }
        }
    }

    go_extra!(C);
}

/// See [`Parser::or_not`].
#[derive(Copy, Clone)]
pub struct OrNot<A> {
    pub(crate) parser: A,
}

// TODO: Maybe implement `IterParser` too?
impl<'a, I, O, E, A> Parser<'a, I, Option<O>, E> for OrNot<A>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, O, E>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, Option<O>> {
        let before = inp.save();
        Ok(match self.parser.go::<M>(inp) {
            Ok(out) => M::map::<O, _, _>(out, Some),
            Err(()) => {
                inp.rewind(before);
                M::bind::<Option<O>, _>(|| None)
            }
        })
    }

    go_extra!(Option<O>);
}

/// See [`Parser::not`].
pub struct Not<A, OA> {
    pub(crate) parser: A,
    pub(crate) phantom: PhantomData<OA>,
}

impl<A: Copy, OA> Copy for Not<A, OA> {}
impl<A: Clone, OA> Clone for Not<A, OA> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, A, OA> Parser<'a, I, (), E> for Not<A, OA>
where
    I: ValueInput<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, ()> {
        let before = inp.save();

        let alt = inp.errors.alt.take();

        let result = self.parser.go::<Check>(inp);
        // SAFETY: Using offsets derived from input
        let result_span = unsafe { inp.span_since(before.offset) };
        inp.rewind(before);

        inp.errors.alt = alt;

        match result {
            Ok(()) => {
                let (at, found) = inp.next();
                inp.add_alt(Located::at(
                    at.into(),
                    E::Error::expected_found(None, found.map(|f| f.into()), result_span),
                ));
                Err(())
            }
            Err(()) => Ok(M::bind(|| ())),
        }
    }

    go_extra!(());
}

/// See [`Parser::and_is`].
pub struct AndIs<A, B, OB> {
    pub(crate) parser_a: A,
    pub(crate) parser_b: B,
    pub(crate) phantom: PhantomData<OB>,
}

impl<A: Copy, B: Copy, OB> Copy for AndIs<A, B, OB> {}
impl<A: Clone, B: Clone, OB> Clone for AndIs<A, B, OB> {
    fn clone(&self) -> Self {
        Self {
            parser_a: self.parser_a.clone(),
            parser_b: self.parser_b.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, A, B, OA, OB> Parser<'a, I, OA, E> for AndIs<A, B, OB>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
    B: Parser<'a, I, OB, E>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, OA> {
        let before = inp.save();
        match self.parser_a.go::<M>(inp) {
            Ok(out) => {
                // A succeeded -- go back to the beginning and try B
                let after = inp.save();
                inp.rewind(before);

                match self.parser_b.go::<Check>(inp) {
                    Ok(()) => {
                        // B succeeded -- go to the end of A and return its output
                        inp.rewind(after);
                        Ok(out)
                    }
                    Err(()) => {
                        // B failed -- go back to the beginning and fail
                        inp.rewind(before);
                        Err(())
                    }
                }
            }
            Err(()) => {
                // A failed -- go back to the beginning and fail
                inp.rewind(before);
                Err(())
            }
        }
    }

    go_extra!(OA);
}

/// See [`Parser::repeated_exactly`].
pub struct RepeatedExactly<A, OA, C, const N: usize> {
    pub(crate) parser: A,
    pub(crate) phantom: PhantomData<(OA, C)>,
}

impl<A: Copy, OA, C, const N: usize> Copy for RepeatedExactly<A, OA, C, N> {}
impl<A: Clone, OA, C, const N: usize> Clone for RepeatedExactly<A, OA, C, N> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            phantom: PhantomData,
        }
    }
}

impl<A, OA, C, const N: usize> RepeatedExactly<A, OA, C, N> {
    /// Set the type of [`ContainerExactly`] to collect into.
    pub fn collect<'a, I, E, D>(self) -> RepeatedExactly<A, OA, D, N>
    where
        A: Parser<'a, I, OA, E>,
        I: Input<'a>,
        E: ParserExtra<'a, I>,
        D: ContainerExactly<OA, N>,
    {
        RepeatedExactly {
            parser: self.parser,
            phantom: PhantomData,
        }
    }
}

// TODO: Work out how this can properly integrate into `IterParser`
impl<'a, I, E, A, OA, C, const N: usize> Parser<'a, I, C, E> for RepeatedExactly<A, OA, C, N>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
    C: ContainerExactly<OA, N>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, C> {
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
                Err(()) => {
                    inp.rewind(before);
                    // SAFETY: All entries with an index < i are filled
                    unsafe {
                        M::map(output, |mut output| C::drop_before(&mut output, i));
                    }
                    break Err(());
                }
            }
        }
    }

    go_extra!(C);
}

/// See [`Parser::separated_by_exactly`].
pub struct SeparatedByExactly<A, B, OB, C, const N: usize> {
    pub(crate) parser: A,
    pub(crate) separator: B,
    pub(crate) allow_leading: bool,
    pub(crate) allow_trailing: bool,
    pub(crate) phantom: PhantomData<(OB, C)>,
}

impl<A: Copy, B: Copy, OB, C, const N: usize> Copy for SeparatedByExactly<A, B, OB, C, N> {}
impl<A: Clone, B: Clone, OB, C, const N: usize> Clone for SeparatedByExactly<A, B, OB, C, N> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            separator: self.separator.clone(),
            allow_leading: self.allow_leading,
            allow_trailing: self.allow_trailing,
            phantom: PhantomData,
        }
    }
}

impl<A, B, OB, C, const N: usize> SeparatedByExactly<A, B, OB, C, N> {
    /// Allow a leading separator to appear before the first item.
    ///
    /// Note that even if no items are parsed, a leading separator *is* permitted.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::prelude::*;
    /// let r#enum = text::keyword::<_, _, _, extra::Err<Simple<char>>>("enum")
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
    /// # use chumsky::prelude::*;
    /// let numbers = text::int::<_, _, extra::Err<Simple<char>>>(10)
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
    pub fn collect<'a, I, OA, E, D>(self) -> SeparatedByExactly<A, B, OB, D, N>
    where
        A: Parser<'a, I, OA, E>,
        I: Input<'a>,
        E: ParserExtra<'a, I>,
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
impl<'a, I, E, A, B, OA, OB, C, const N: usize> Parser<'a, I, [OA; N], E>
    for SeparatedByExactly<A, B, OB, C, N>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
    B: Parser<'a, I, OB, E>,
    C: ContainerExactly<OA, N>,
{
    // FIXME: why parse result output is not C ?
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, [OA; N]> {
        if self.allow_leading {
            let before_separator = inp.save();
            if let Err(()) = self.separator.go::<Check>(inp) {
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
                            if self.separator.go::<Check>(inp).is_err() {
                                inp.rewind(before_separator);
                            }
                        }

                        // SAFETY: All entries with an index < i are filled
                        break Ok(M::array::<OA, N>(unsafe {
                            MaybeUninitExt::array_assume_init(output)
                        }));
                    } else {
                        let before_separator = inp.save();
                        if self.separator.go::<Check>(inp).is_err() {
                            inp.rewind(before_separator);
                            // SAFETY: All entries with an index < i are filled
                            output[..i]
                                .iter_mut()
                                .for_each(|o| unsafe { o.assume_init_drop() });
                            break Err(());
                        }
                    }
                }
                Err(()) => {
                    inp.rewind(before);
                    // SAFETY: All entries with an index < i are filled
                    output[..i]
                        .iter_mut()
                        .for_each(|o| unsafe { o.assume_init_drop() });
                    break Err(());
                }
            }
        }
    }

    go_extra!([OA; N]);
}

/// See [`IterParser::foldr`].
pub struct Foldr<F, A, B, OA, E> {
    pub(crate) parser_a: A,
    pub(crate) parser_b: B,
    pub(crate) folder: F,
    pub(crate) phantom: PhantomData<(OA, E)>,
}

impl<F: Copy, A: Copy, B: Copy, OA, E> Copy for Foldr<F, A, B, OA, E> {}
impl<F: Clone, A: Clone, B: Clone, OA, E> Clone for Foldr<F, A, B, OA, E> {
    fn clone(&self) -> Self {
        Self {
            parser_a: self.parser_a.clone(),
            parser_b: self.parser_b.clone(),
            folder: self.folder.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, F, A, B, O, OA, E> Parser<'a, I, O, E> for Foldr<F, A, B, OA, E>
where
    I: Input<'a>,
    A: IterParser<'a, I, OA, E>,
    B: Parser<'a, I, O, E>,
    E: ParserExtra<'a, I>,
    F: Fn(OA, O) -> O,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O>
    where
        Self: Sized,
    {
        let mut a_out = M::bind(|| Vec::new());
        let mut iter_state = self.parser_a.make_iter::<M>(inp)?;
        loop {
            match self.parser_a.next::<M>(inp, &mut iter_state) {
                Ok(Some(out)) => {
                    a_out = M::combine(a_out, out, |mut a_out, item| {
                        a_out.push(item);
                        a_out
                    });
                }
                Ok(None) => break,
                Err(()) => return Err(()),
            }
        }

        let b_out = self.parser_b.go::<M>(inp)?;

        Ok(M::combine(a_out, b_out, |a_out, b_out| {
            a_out.into_iter().rfold(b_out, |b, a| (self.folder)(a, b))
        }))
    }

    go_extra!(O);
}

/// See [`Parser::foldl`].
pub struct Foldl<F, A, B, OB, E> {
    pub(crate) parser_a: A,
    pub(crate) parser_b: B,
    pub(crate) folder: F,
    pub(crate) phantom: PhantomData<(OB, E)>,
}

impl<F: Copy, A: Copy, B: Copy, OB, E> Copy for Foldl<F, A, B, OB, E> {}
impl<F: Clone, A: Clone, B: Clone, OB, E> Clone for Foldl<F, A, B, OB, E> {
    fn clone(&self) -> Self {
        Self {
            parser_a: self.parser_a.clone(),
            parser_b: self.parser_b.clone(),
            folder: self.folder.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, F, A, B, O, OB, E> Parser<'a, I, O, E> for Foldl<F, A, B, OB, E>
where
    I: Input<'a>,
    A: Parser<'a, I, O, E>,
    B: IterParser<'a, I, OB, E>,
    E: ParserExtra<'a, I>,
    F: Fn(O, OB) -> O,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O>
    where
        Self: Sized,
    {
        let mut out = self.parser_a.go::<M>(inp)?;
        let mut iter_state = self.parser_b.make_iter::<M>(inp)?;
        loop {
            match self.parser_b.next::<M>(inp, &mut iter_state) {
                Ok(Some(b_out)) => {
                    out = M::combine(out, b_out, |out, b_out| (self.folder)(out, b_out));
                }
                Ok(None) => break Ok(out),
                Err(()) => break Err(()),
            }
        }
    }

    go_extra!(O);
}

/// See [`Parser::rewind`].
#[must_use]
#[derive(Copy, Clone)]
pub struct Rewind<A> {
    pub(crate) parser: A,
}

impl<'a, I, O, E, A> Parser<'a, I, O, E> for Rewind<A>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, O, E>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        let before = inp.save();
        match self.parser.go::<M>(inp) {
            Ok(out) => {
                inp.rewind(before);
                Ok(out)
            }
            Err(()) => Err(()),
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

impl<'a, I, O, E, A, F> Parser<'a, I, O, E> for MapErr<A, F>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, O, E>,
    F: Fn(E::Error) -> E::Error,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O>
    where
        Self: Sized,
    {
        let res = self.parser.go::<M>(inp);

        if res.is_err() {
            let mut e = inp.errors.alt.take().expect("error but no alt?");
            e.err = (self.mapper)(e.err);
            inp.errors.alt = Some(e);
        }

        res
    }

    go_extra!(O);
}

/// See [`Parser::map_err_with_span`].
#[derive(Copy, Clone)]
pub struct MapErrWithSpan<A, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
}

impl<'a, I, O, E, A, F> Parser<'a, I, O, E> for MapErrWithSpan<A, F>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, O, E>,
    F: Fn(E::Error, I::Span) -> E::Error,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O>
    where
        Self: Sized,
    {
        let start = inp.offset();
        let res = self.parser.go::<M>(inp);

        if res.is_err() {
            let mut e = inp.errors.alt.take().expect("error but no alt?");
            // SAFETY: Using offsets derived from input
            let span = unsafe { inp.span_since(start) };
            e.err = (self.mapper)(e.err, span);
        }

        res
    }

    go_extra!(O);
}

/// See [`Parser::map_err_with_state`].
#[derive(Copy, Clone)]
pub struct MapErrWithState<A, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
}

impl<'a, I, O, E, A, F> Parser<'a, I, O, E> for MapErrWithState<A, F>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, O, E>,
    F: Fn(E::Error, I::Span, &mut E::State) -> E::Error,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O>
    where
        Self: Sized,
    {
        let start = inp.offset();
        let res = self.parser.go::<M>(inp);

        if res.is_err() {
            let mut e = inp.errors.alt.take().expect("error but no alt?");
            // SAFETY: Using offsets derived from input
            let span = unsafe { inp.span_since(start) };
            e.err = (self.mapper)(e.err, span, inp.state());
        }

        res
    }

    go_extra!(O);
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

impl<'a, I, OA, U, E, A, F> Parser<'a, I, U, E> for Validate<A, OA, F>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
    F: Fn(OA, I::Span, &mut Emitter<E::Error>) -> U,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, U>
    where
        Self: Sized,
    {
        let before = inp.offset();
        self.parser.go::<Emit>(inp).map(|out| {
            // SAFETY: Using offsets derived from input
            let span = unsafe { inp.span_since(before) };
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

impl<'a, I, O, E, A, F> Parser<'a, I, O, E> for OrElse<A, F>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, O, E>,
    F: Fn(E::Error) -> Result<O, E::Error>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O>
    where
        Self: Sized,
    {
        let before = inp.save();
        match self.parser.go::<M>(inp) {
            Ok(out) => Ok(out),
            Err(()) => {
                let err = inp.errors.alt.take().expect("error but no alt?");
                match (self.or_else)(err.err) {
                    Ok(out) => {
                        inp.rewind(before);
                        Ok(M::bind(|| out))
                    }
                    Err(new_err) => {
                        inp.errors.alt = Some(Located {
                            pos: err.pos,
                            err: new_err,
                        });
                        Err(())
                    }
                }
            }
        }
    }

    go_extra!(O);
}

#[cfg(test)]
mod tests {
    use crate::prelude::*;

    #[test]
    fn separated_by_at_least() {
        let parser = just::<_, _, extra::Default>('-')
            .separated_by(just(','))
            .at_least(3)
            .collect();

        assert_eq!(parser.parse("-,-,-").into_result(), Ok(vec!['-', '-', '-']));
    }

    #[test]
    fn separated_by_at_least_without_leading() {
        let parser = just::<_, _, extra::Default>('-')
            .separated_by(just(','))
            .at_least(3)
            .collect::<Vec<_>>();

        // Is empty means no errors
        assert!(parser.parse(",-,-,-").has_errors());
    }

    #[test]
    fn separated_by_at_least_without_trailing() {
        let parser = just::<_, _, extra::Default>('-')
            .separated_by(just(','))
            .at_least(3)
            .collect::<Vec<_>>();

        // Is empty means no errors
        assert!(parser.parse("-,-,-,").has_errors());
    }

    #[test]
    fn separated_by_at_least_with_leading() {
        let parser = just::<_, _, extra::Default>('-')
            .separated_by(just(','))
            .allow_leading()
            .at_least(3)
            .collect();

        assert_eq!(
            parser.parse(",-,-,-").into_result(),
            Ok(vec!['-', '-', '-'])
        );
        assert!(parser.parse(",-,-").has_errors());
    }

    #[test]
    fn separated_by_at_least_with_trailing() {
        let parser = just::<_, _, extra::Default>('-')
            .separated_by(just(','))
            .allow_trailing()
            .at_least(3)
            .collect();

        assert_eq!(
            parser.parse("-,-,-,").into_result(),
            Ok(vec!['-', '-', '-'])
        );
        assert!(parser.parse("-,-,").has_errors());
    }

    #[test]
    fn separated_by_leaves_last_separator() {
        let parser = just::<_, _, extra::Default>('-')
            .separated_by(just(','))
            .collect::<Vec<_>>()
            .then(just(','));
        assert_eq!(
            parser.parse("-,-,-,").into_result(),
            Ok((vec!['-', '-', '-'], ',')),
        )
    }
}
