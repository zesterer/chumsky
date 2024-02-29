//! Combinators that allow combining and extending existing parsers.
//!
//! *“Ford... you're turning into a penguin. Stop it.”*
//!
//! Although it's *sometimes* useful to be able to name their type, most of these parsers are much easier to work with
//! when accessed through their respective methods on [`Parser`].

use super::*;

/// The type of a lazy parser.
pub type Lazy<'a, A, I, E> =
    ThenIgnore<A, Repeated<Any<I, E>, <I as Input<'a>>::Token, I, E>, (), E>;

/// Alter the configuration of a struct using parse-time context
#[derive(Copy, Clone)]
pub struct Configure<A, F> {
    pub(crate) parser: A,
    pub(crate) cfg: F,
}

impl<'a, I, O, E, A, F> ParserSealed<'a, I, O, E> for Configure<A, F>
where
    A: ConfigParser<'a, I, O, E>,
    F: Fn(A::Config, &E::Context) -> A::Config,
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    #[inline(always)]
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
    #[allow(dead_code)]
    pub(crate) phantom: EmptyPhantom<OA>,
}

impl<A: Copy, F: Copy, OA> Copy for IterConfigure<A, F, OA> {}
impl<A: Clone, F: Clone, OA> Clone for IterConfigure<A, F, OA> {
    fn clone(&self) -> Self {
        IterConfigure {
            parser: self.parser.clone(),
            cfg: self.cfg.clone(),
            phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, I, OA, E, A, F> ParserSealed<'a, I, (), E> for IterConfigure<A, F, OA>
where
    A: ConfigIterParser<'a, I, OA, E>,
    F: Fn(A::Config, &E::Context) -> A::Config,
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    #[inline(always)]
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

impl<'a, I, O, E, A, F> IterParserSealed<'a, I, O, E> for IterConfigure<A, F, O>
where
    A: ConfigIterParser<'a, I, O, E>,
    F: Fn(A::Config, &E::Context) -> A::Config,
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    type IterState<M: Mode> = (A::IterState<M>, A::Config)
    where
        I: 'a;

    #[inline(always)]
    fn make_iter<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
    ) -> PResult<Emit, Self::IterState<M>> {
        Ok((
            A::make_iter(&self.parser, inp)?,
            (self.cfg)(A::Config::default(), inp.ctx()),
        ))
    }

    #[inline(always)]
    fn next<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        state: &mut Self::IterState<M>,
    ) -> IPResult<M, O> {
        self.parser.next_cfg(inp, &mut state.0, &state.1)
    }
}

/// See [`ConfigIterParser::try_configure`]
pub struct TryIterConfigure<A, F, O> {
    pub(crate) parser: A,
    pub(crate) cfg: F,
    #[allow(dead_code)]
    pub(crate) phantom: EmptyPhantom<O>,
}

impl<A: Copy, F: Copy, O> Copy for TryIterConfigure<A, F, O> {}
impl<A: Clone, F: Clone, O> Clone for TryIterConfigure<A, F, O> {
    fn clone(&self) -> Self {
        TryIterConfigure {
            parser: self.parser.clone(),
            cfg: self.cfg.clone(),
            phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, I, OA, E, A, F> ParserSealed<'a, I, (), E> for TryIterConfigure<A, F, OA>
where
    A: ConfigIterParser<'a, I, OA, E>,
    F: Fn(A::Config, &E::Context, I::Span) -> Result<A::Config, E::Error>,
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    #[inline(always)]
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

impl<'a, I, O, E, A, F> IterParserSealed<'a, I, O, E> for TryIterConfigure<A, F, O>
where
    A: ConfigIterParser<'a, I, O, E>,
    F: Fn(A::Config, &E::Context, I::Span) -> Result<A::Config, E::Error>,
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
        let cfg = (self.cfg)(
            A::Config::default(),
            inp.ctx(),
            inp.span_since(inp.offset()),
        )
        .map_err(|e| inp.add_alt_err(inp.offset, e))?;

        Ok((A::make_iter(&self.parser, inp)?, cfg))
    }

    fn next<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        state: &mut Self::IterState<M>,
    ) -> IPResult<M, O> {
        self.parser.next_cfg(inp, &mut state.0, &state.1)
    }
}

/// See [`Parser::to_slice`]
pub struct ToSlice<A, O> {
    pub(crate) parser: A,
    #[allow(dead_code)]
    pub(crate) phantom: EmptyPhantom<O>,
}

impl<A: Copy, O> Copy for ToSlice<A, O> {}
impl<A: Clone, O> Clone for ToSlice<A, O> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, A, I, O, E> ParserSealed<'a, I, I::Slice, E> for ToSlice<A, O>
where
    A: Parser<'a, I, O, E>,
    I: SliceInput<'a>,
    E: ParserExtra<'a, I>,
{
    #[inline(always)]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, I::Slice>
    where
        Self: Sized,
    {
        let before = inp.offset();
        self.parser.go::<Check>(inp)?;

        Ok(M::bind(|| inp.slice_since(before..)))
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

impl<'a, A, I, O, E, F> ParserSealed<'a, I, O, E> for Filter<A, F>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, O, E>,
    F: Fn(&O) -> bool,
{
    #[inline(always)]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        let before = inp.offset();
        self.parser.go::<Emit>(inp).and_then(|out| {
            if (self.filter)(&out) {
                Ok(M::bind(|| out))
            } else {
                let err_span = inp.span_since(before);
                inp.add_alt(inp.offset().offset, None, None, err_span);
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
    #[allow(dead_code)]
    pub(crate) phantom: EmptyPhantom<OA>,
}

impl<A: Copy, OA, F: Copy> Copy for Map<A, OA, F> {}
impl<A: Clone, OA, F: Clone> Clone for Map<A, OA, F> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            mapper: self.mapper.clone(),
            phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, I, O, E, A, OA, F> ParserSealed<'a, I, O, E> for Map<A, OA, F>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
    F: Fn(OA) -> O,
{
    #[inline(always)]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        let out = self.parser.go::<M>(inp)?;
        Ok(M::map(out, &self.mapper))
    }

    go_extra!(O);
}

impl<'a, I, O, E, A, OA, F> IterParserSealed<'a, I, O, E> for Map<A, OA, F>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: IterParser<'a, I, OA, E>,
    F: Fn(OA) -> O,
{
    type IterState<M: Mode> = A::IterState<M>
    where
        I: 'a;

    #[inline(always)]
    fn make_iter<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
    ) -> PResult<Emit, Self::IterState<M>> {
        self.parser.make_iter(inp)
    }

    #[inline(always)]
    fn next<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        state: &mut Self::IterState<M>,
    ) -> IPResult<M, O> {
        match self.parser.next::<M>(inp, state) {
            Ok(Some(o)) => Ok(Some(M::map(o, &self.mapper))),
            Ok(None) => Ok(None),
            Err(()) => Err(()),
        }
    }
}

/// See [`Parser::map_with`].
pub struct MapWith<A, OA, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
    #[allow(dead_code)]
    pub(crate) phantom: EmptyPhantom<OA>,
}

impl<A: Copy, OA, F: Copy> Copy for MapWith<A, OA, F> {}
impl<A: Clone, OA, F: Clone> Clone for MapWith<A, OA, F> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            mapper: self.mapper.clone(),
            phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, I, O, E, A, OA, F> ParserSealed<'a, I, O, E> for MapWith<A, OA, F>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
    F: Fn(OA, &mut MapExtra<'a, '_, '_, I, E>) -> O,
{
    #[inline(always)]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        let before = inp.offset();
        let out = self.parser.go::<M>(inp)?;
        Ok(M::map(out, |out| {
            (self.mapper)(out, &mut MapExtra::new(before, inp))
        }))
    }

    go_extra!(O);
}

impl<'a, I, O, E, A, OA, F> IterParserSealed<'a, I, O, E> for MapWith<A, OA, F>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: IterParser<'a, I, OA, E>,
    F: Fn(OA, &mut MapExtra<'a, '_, '_, I, E>) -> O,
{
    type IterState<M: Mode> = A::IterState<M>
    where
        I: 'a;

    #[inline(always)]
    fn make_iter<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
    ) -> PResult<Emit, Self::IterState<M>> {
        self.parser.make_iter(inp)
    }

    #[inline(always)]
    fn next<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        state: &mut Self::IterState<M>,
    ) -> IPResult<M, O> {
        let before = inp.offset();
        match self.parser.next::<M>(inp, state) {
            Ok(Some(o)) => Ok(Some(M::map(o, |o| {
                (self.mapper)(o, &mut MapExtra::new(before, inp))
            }))),
            Ok(None) => Ok(None),
            Err(()) => Err(()),
        }
    }
}

/// See [`Parser::map_group`].
#[cfg(feature = "nightly")]
pub struct MapGroup<A, OA, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
    #[allow(dead_code)]
    pub(crate) phantom: EmptyPhantom<OA>,
}

#[cfg(feature = "nightly")]
impl<A: Copy, OA, F: Copy> Copy for MapGroup<A, OA, F> {}
#[cfg(feature = "nightly")]
impl<A: Clone, OA, F: Clone> Clone for MapGroup<A, OA, F> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            mapper: self.mapper.clone(),
            phantom: EmptyPhantom::new(),
        }
    }
}

#[cfg(feature = "nightly")]
impl<'a, I, O, E, A, OA, F> ParserSealed<'a, I, O, E> for MapGroup<A, OA, F>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
    F: Fn<OA, Output = O>,
    OA: Tuple,
{
    #[inline(always)]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        let out = self.parser.go::<M>(inp)?;
        Ok(M::map(out, |out| self.mapper.call(out)))
    }

    go_extra!(O);
}

#[cfg(feature = "nightly")]
impl<'a, I, O, E, A, OA, F> IterParserSealed<'a, I, O, E> for MapGroup<A, OA, F>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: IterParser<'a, I, OA, E>,
    F: Fn<OA, Output = O>,
    OA: Tuple,
{
    type IterState<M: Mode> = A::IterState<M>
    where
        I: 'a;

    #[inline(always)]
    fn make_iter<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
    ) -> PResult<Emit, Self::IterState<M>> {
        self.parser.make_iter(inp)
    }

    #[inline(always)]
    fn next<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        state: &mut Self::IterState<M>,
    ) -> IPResult<M, O> {
        match self.parser.next::<M>(inp, state) {
            Ok(Some(o)) => Ok(Some(M::map(o, |o| self.mapper.call(o)))),
            Ok(None) => Ok(None),
            Err(()) => Err(()),
        }
    }
}

/// See [`Parser::to_span`].
pub struct ToSpan<A, OA> {
    pub(crate) parser: A,
    #[allow(dead_code)]
    pub(crate) phantom: EmptyPhantom<OA>,
}

impl<A: Copy, OA> Copy for ToSpan<A, OA> {}
impl<A: Clone, OA> Clone for ToSpan<A, OA> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, I, OA, E, A> ParserSealed<'a, I, I::Span, E> for ToSpan<A, OA>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
{
    #[inline(always)]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, I::Span> {
        let before = inp.offset();
        self.parser.go::<M>(inp)?;
        Ok(M::bind(|| inp.span_since(before)))
    }

    go_extra!(I::Span);
}

/// See [`Parser::try_map`].
pub struct TryMap<A, OA, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
    #[allow(dead_code)]
    pub(crate) phantom: EmptyPhantom<OA>,
}

impl<A: Copy, OA, F: Copy> Copy for TryMap<A, OA, F> {}
impl<A: Clone, OA, F: Clone> Clone for TryMap<A, OA, F> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            mapper: self.mapper.clone(),
            phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, I, O, E, A, OA, F> ParserSealed<'a, I, O, E> for TryMap<A, OA, F>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
    F: Fn(OA, I::Span) -> Result<O, E::Error>,
{
    #[inline(always)]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        let before = inp.offset();
        let out = self.parser.go::<Emit>(inp)?;
        let span = inp.span_since(before);
        match (self.mapper)(out, span) {
            Ok(out) => Ok(M::bind(|| out)),
            Err(err) => {
                inp.add_alt_err(before.offset, err);
                Err(())
            }
        }
    }

    go_extra!(O);
}

/// See [`Parser::try_map_with`].
pub struct TryMapWith<A, OA, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
    #[allow(dead_code)]
    pub(crate) phantom: EmptyPhantom<OA>,
}

impl<A: Copy, OA, F: Copy> Copy for TryMapWith<A, OA, F> {}
impl<A: Clone, OA, F: Clone> Clone for TryMapWith<A, OA, F> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            mapper: self.mapper.clone(),
            phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, I, O, E, A, OA, F> ParserSealed<'a, I, O, E> for TryMapWith<A, OA, F>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
    F: Fn(OA, &mut MapExtra<'a, '_, '_, I, E>) -> Result<O, E::Error>,
{
    #[inline(always)]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        let before = inp.offset();
        let out = self.parser.go::<Emit>(inp)?;
        match (self.mapper)(out, &mut MapExtra::new(before, inp)) {
            Ok(out) => Ok(M::bind(|| out)),
            Err(err) => {
                inp.add_alt_err(inp.offset().offset, err);
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
    #[allow(dead_code)]
    pub(crate) phantom: EmptyPhantom<OA>,
}

impl<A: Copy, OA, O: Copy> Copy for To<A, OA, O> {}
impl<A: Clone, OA, O: Clone> Clone for To<A, OA, O> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            to: self.to.clone(),
            phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, I, O, E, A, OA> ParserSealed<'a, I, O, E> for To<A, OA, O>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
    O: Clone,
{
    #[inline(always)]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        self.parser.go::<Check>(inp)?;
        Ok(M::bind(|| self.to.clone()))
    }

    go_extra!(O);
}

/// See [`Parser::into_iter`].
pub struct IntoIter<A, O> {
    pub(crate) parser: A,
    #[allow(dead_code)]
    pub(crate) phantom: EmptyPhantom<O>,
}

impl<A: Copy, O> Copy for IntoIter<A, O> {}
impl<A: Clone, O> Clone for IntoIter<A, O> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, A, O, I, E> IterParserSealed<'a, I, O::Item, E> for IntoIter<A, O>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, O, E>,
    O: IntoIterator,
{
    // TODO: Don't always produce output for non-emitting modes, but needed due to length. Use some way to 'select'
    // between iterator and usize at compile time.
    type IterState<M: Mode> = O::IntoIter; //M::Output<O::IntoIter>;

    const NONCONSUMPTION_IS_OK: bool = true;

    #[inline(always)]
    fn make_iter<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
    ) -> PResult<Emit, Self::IterState<M>> {
        // M::map(self.parser.go::<M>(inp)?, |out| out.into_iter())
        self.parser.go::<Emit>(inp).map(|out| out.into_iter())
    }

    #[inline(always)]
    fn next<M: Mode>(
        &self,
        _inp: &mut InputRef<'a, '_, I, E>,
        iter: &mut Self::IterState<M>,
    ) -> IPResult<M, O::Item> {
        Ok(iter.next().map(|out| M::bind(|| out)))
    }
}

/// See [`Parser::ignored`].
pub struct Ignored<A, OA> {
    pub(crate) parser: A,
    #[allow(dead_code)]
    pub(crate) phantom: EmptyPhantom<OA>,
}

impl<A: Copy, OA> Copy for Ignored<A, OA> {}
impl<A: Clone, OA> Clone for Ignored<A, OA> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, I, E, A, OA> ParserSealed<'a, I, (), E> for Ignored<A, OA>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
{
    #[inline(always)]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, ()> {
        self.parser.go::<Check>(inp)?;
        Ok(M::bind(|| ()))
    }

    go_extra!(());
}

/// See [`Parser::unwrapped`].
pub struct Unwrapped<A, O> {
    pub(crate) parser: A,
    pub(crate) location: Location<'static>,
    #[allow(dead_code)]
    pub(crate) phantom: EmptyPhantom<O>,
}

impl<A: Copy, O> Copy for Unwrapped<A, O> {}
impl<A: Clone, O> Clone for Unwrapped<A, O> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            location: self.location,
            phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, I, E, A, O, U> ParserSealed<'a, I, O, E> for Unwrapped<A, Result<O, U>>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, Result<O, U>, E>,
    U: fmt::Debug,
{
    #[inline(always)]
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

impl<'a, I, E, A, O> ParserSealed<'a, I, O, E> for Unwrapped<A, Option<O>>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, Option<O>, E>,
{
    #[inline(always)]
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

/// See [`Parser::memoized`].
#[cfg(feature = "memoization")]
#[derive(Copy, Clone)]
pub struct Memoized<A> {
    pub(crate) parser: A,
}

#[cfg(feature = "memoization")]
impl<'a, I, E, A, O> ParserSealed<'a, I, O, E> for Memoized<A>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    E::Error: Clone,
    A: Parser<'a, I, O, E>,
{
    #[inline(always)]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        let before = inp.offset();
        // TODO: Don't use address, since this might not be constant?
        let key = (
            before.offset,
            &self.parser as *const _ as *const () as usize,
        );

        match inp.memos.entry(key) {
            hashbrown::hash_map::Entry::Occupied(o) => {
                if let Some(err) = o.get() {
                    let err = err.clone();
                    inp.add_alt_err(err.pos, err.err);
                } else {
                    let err_span = inp.span_since(before);
                    inp.add_alt(key.0, None, None, err_span);
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
    #[allow(dead_code)]
    pub(crate) phantom: EmptyPhantom<(OA, OB, E)>,
}

impl<A: Copy, B: Copy, OA, OB, E> Copy for Then<A, B, OA, OB, E> {}
impl<A: Clone, B: Clone, OA, OB, E> Clone for Then<A, B, OA, OB, E> {
    fn clone(&self) -> Self {
        Self {
            parser_a: self.parser_a.clone(),
            parser_b: self.parser_b.clone(),
            phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, I, E, A, B, OA, OB> ParserSealed<'a, I, (OA, OB), E> for Then<A, B, OA, OB, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
    B: Parser<'a, I, OB, E>,
{
    #[inline(always)]
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
    #[allow(dead_code)]
    pub(crate) phantom: EmptyPhantom<(OA, E)>,
}

impl<A: Copy, B: Copy, OA, E> Copy for IgnoreThen<A, B, OA, E> {}
impl<A: Clone, B: Clone, OA, E> Clone for IgnoreThen<A, B, OA, E> {
    fn clone(&self) -> Self {
        Self {
            parser_a: self.parser_a.clone(),
            parser_b: self.parser_b.clone(),
            phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, I, E, A, B, OA, OB> ParserSealed<'a, I, OB, E> for IgnoreThen<A, B, OA, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
    B: Parser<'a, I, OB, E>,
{
    #[inline(always)]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, OB> {
        self.parser_a.go::<Check>(inp)?;
        let b = self.parser_b.go::<M>(inp)?;
        Ok(M::map(b, |b: OB| b))
    }

    go_extra!(OB);
}

/// See [`Parser::then_ignore`].
pub struct ThenIgnore<A, B, OB, E> {
    pub(crate) parser_a: A,
    pub(crate) parser_b: B,
    #[allow(dead_code)]
    pub(crate) phantom: EmptyPhantom<(OB, E)>,
}

impl<A: Copy, B: Copy, OB, E> Copy for ThenIgnore<A, B, OB, E> {}
impl<A: Clone, B: Clone, OB, E> Clone for ThenIgnore<A, B, OB, E> {
    fn clone(&self) -> Self {
        Self {
            parser_a: self.parser_a.clone(),
            parser_b: self.parser_b.clone(),
            phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, I, E, A, B, OA, OB> ParserSealed<'a, I, OA, E> for ThenIgnore<A, B, OB, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
    B: Parser<'a, I, OB, E>,
{
    #[inline(always)]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, OA> {
        let a = self.parser_a.go::<M>(inp)?;
        self.parser_b.go::<Check>(inp)?;
        Ok(M::map(a, |a: OA| a))
    }

    go_extra!(OA);
}

/// See [`Parser::nested_in`].
pub struct NestedIn<A, B, O, E> {
    pub(crate) parser_a: A,
    pub(crate) parser_b: B,
    #[allow(dead_code)]
    pub(crate) phantom: EmptyPhantom<(O, E)>,
}

impl<A: Copy, B: Copy, O, E> Copy for NestedIn<A, B, O, E> {}
impl<A: Clone, B: Clone, O, E> Clone for NestedIn<A, B, O, E> {
    fn clone(&self) -> Self {
        Self {
            parser_a: self.parser_a.clone(),
            parser_b: self.parser_b.clone(),
            phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, I, E, A, B, O> ParserSealed<'a, I, O, E> for NestedIn<A, B, O, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, O, E>,
    B: Parser<'a, I, I, E>,
{
    #[inline(always)]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        let inp2 = self.parser_b.go::<Emit>(inp)?;

        let alt = inp.errors.alt.take();

        #[cfg(feature = "memoization")]
        let mut memos = HashMap::default();
        let res = inp.with_input(
            &inp2,
            |inp| (&self.parser_a).then_ignore(end()).go::<M>(inp),
            #[cfg(feature = "memoization")]
            &mut memos,
        );

        // TODO: Translate secondary error offsets too
        let new_alt = inp.errors.alt.take();
        inp.errors.alt = alt;
        if let Some(new_alt) = new_alt {
            inp.add_alt_err(inp.offset().offset, new_alt.err);
        }

        res
    }

    go_extra!(O);
}

/// See [`Parser::ignore_with_ctx`].
pub struct IgnoreWithCtx<A, B, OA, I, E> {
    pub(crate) parser: A,
    pub(crate) then: B,
    #[allow(dead_code)]
    pub(crate) phantom: EmptyPhantom<(B, OA, E, I)>,
}

impl<A: Copy, B: Copy, OA, I, E> Copy for IgnoreWithCtx<A, B, OA, I, E> {}
impl<A: Clone, B: Clone, OA, I, E> Clone for IgnoreWithCtx<A, B, OA, I, E> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            then: self.then.clone(),
            phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, I, E, A, B, OA, OB> ParserSealed<'a, I, OB, E>
    for IgnoreWithCtx<A, B, OA, I, extra::Full<E::Error, E::State, OA>>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
    B: Parser<'a, I, OB, extra::Full<E::Error, E::State, OA>>,
    OA: 'a,
{
    #[inline(always)]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, OB> {
        let p1 = self.parser.go::<Emit>(inp)?;
        inp.with_ctx(&p1, |inp| self.then.go::<M>(inp))
    }

    go_extra!(OB);
}

impl<'a, I, E, A, B, OA, OB> IterParserSealed<'a, I, OB, E>
    for IgnoreWithCtx<A, B, OA, I, extra::Full<E::Error, E::State, OA>>
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

    #[inline(always)]
    fn make_iter<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
    ) -> PResult<Emit, Self::IterState<M>> {
        let out = self.parser.go::<Emit>(inp)?;
        let then = inp.with_ctx(&out, |inp| self.then.make_iter::<M>(inp))?;
        Ok((out, then))
    }

    #[inline(always)]
    fn next<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        state: &mut Self::IterState<M>,
    ) -> IPResult<M, OB> {
        let (ctx, inner_state) = state;

        inp.with_ctx(ctx, |inp| self.then.next(inp, inner_state))
    }
}

/// See [`Parser::then_with_ctx`].
pub struct ThenWithCtx<A, B, OA, I, E> {
    pub(crate) parser: A,
    pub(crate) then: B,
    #[allow(dead_code)]
    pub(crate) phantom: EmptyPhantom<(B, OA, E, I)>,
}

impl<A: Copy, B: Copy, OA, I, E> Copy for ThenWithCtx<A, B, OA, I, E> {}
impl<A: Clone, B: Clone, OA, I, E> Clone for ThenWithCtx<A, B, OA, I, E> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            then: self.then.clone(),
            phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, I, E, A, B, OA, OB> ParserSealed<'a, I, (OA, OB), E>
    for ThenWithCtx<A, B, OA, I, extra::Full<E::Error, E::State, OA>>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
    B: Parser<'a, I, OB, extra::Full<E::Error, E::State, OA>>,
    OA: 'a,
{
    #[inline(always)]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, (OA, OB)> {
        let p1 = self.parser.go::<Emit>(inp)?;
        let p2 = inp.with_ctx(&p1, |inp| self.then.go::<M>(inp))?;
        Ok(M::map(p2, |p2| (p1, p2)))
    }

    go_extra!((OA, OB));
}

impl<'a, I, E, A, B, OA, OB> IterParserSealed<'a, I, OB, E>
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

    #[inline(always)]
    fn make_iter<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
    ) -> PResult<Emit, Self::IterState<M>> {
        let out = self.parser.go::<Emit>(inp)?;
        let then = inp.with_ctx(&out, |inp| self.then.make_iter::<M>(inp))?;
        Ok((out, then))
    }

    #[inline(always)]
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

impl<'a, I, O, E, A, Ctx> ParserSealed<'a, I, O, E> for WithCtx<A, Ctx>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, O, extra::Full<E::Error, E::State, Ctx>>,
    Ctx: 'a,
{
    #[inline(always)]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        inp.with_ctx(&self.ctx, |inp| self.parser.go::<M>(inp))
    }

    go_extra!(O);
}

/// See [`Parser::with_state`].
pub struct WithState<A, State> {
    pub(crate) parser: A,
    pub(crate) state: State,
}

impl<A: Copy, Ctx: Copy> Copy for WithState<A, Ctx> {}
impl<A: Clone, Ctx: Clone> Clone for WithState<A, Ctx> {
    fn clone(&self) -> Self {
        WithState {
            parser: self.parser.clone(),
            state: self.state.clone(),
        }
    }
}

impl<'a, I, O, E, A, State> ParserSealed<'a, I, O, E> for WithState<A, State>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, O, extra::Full<E::Error, State, E::Context>>,
    State: 'a + Clone,
{
    #[inline(always)]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        inp.with_state(&mut self.state.clone(), |inp| self.parser.go::<M>(inp))
    }

    go_extra!(O);
}

/// See [`Parser::delimited_by`].
pub struct DelimitedBy<A, B, C, OB, OC> {
    pub(crate) parser: A,
    pub(crate) start: B,
    pub(crate) end: C,
    #[allow(dead_code)]
    pub(crate) phantom: EmptyPhantom<(OB, OC)>,
}

impl<A: Copy, B: Copy, C: Copy, OB, OC> Copy for DelimitedBy<A, B, C, OB, OC> {}
impl<A: Clone, B: Clone, C: Clone, OB, OC> Clone for DelimitedBy<A, B, C, OB, OC> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            start: self.start.clone(),
            end: self.end.clone(),
            phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, I, E, A, B, C, OA, OB, OC> ParserSealed<'a, I, OA, E> for DelimitedBy<A, B, C, OB, OC>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
    B: Parser<'a, I, OB, E>,
    C: Parser<'a, I, OC, E>,
{
    #[inline(always)]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, OA> {
        self.start.go::<Check>(inp)?;
        let a = self.parser.go::<M>(inp)?;
        self.end.go::<Check>(inp)?;
        Ok(a)
    }

    go_extra!(OA);
}

/// See [`Parser::padded_by`].
pub struct PaddedBy<A, B, OB> {
    pub(crate) parser: A,
    pub(crate) padding: B,
    #[allow(dead_code)]
    pub(crate) phantom: EmptyPhantom<OB>,
}

impl<A: Copy, B: Copy, OB> Copy for PaddedBy<A, B, OB> {}
impl<A: Clone, B: Clone, OB> Clone for PaddedBy<A, B, OB> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            padding: self.padding.clone(),
            phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, I, E, A, B, OA, OB> ParserSealed<'a, I, OA, E> for PaddedBy<A, B, OB>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
    B: Parser<'a, I, OB, E>,
{
    #[inline(always)]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, OA> {
        self.padding.go::<Check>(inp)?;
        let a = self.parser.go::<M>(inp)?;
        self.padding.go::<Check>(inp)?;
        Ok(a)
    }

    go_extra!(OA);
}

/// See [`Parser::or`].
#[derive(Copy, Clone)]
pub struct Or<A, B> {
    pub(crate) choice: crate::primitive::Choice<(A, B)>,
}

impl<'a, I, O, E, A, B> ParserSealed<'a, I, O, E> for Or<A, B>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, O, E>,
    B: Parser<'a, I, O, E>,
{
    #[inline(always)]
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
pub struct Repeated<A, OA, I, E> {
    pub(crate) parser: A,
    pub(crate) at_least: usize,
    // Slightly evil: Should be `Option<usize>`, but we encode `!0` as 'no cap' because it's so large
    pub(crate) at_most: u64,
    #[cfg(debug_assertions)]
    pub(crate) location: Location<'static>,
    #[allow(dead_code)]
    pub(crate) phantom: EmptyPhantom<(OA, E, I)>,
}

impl<A: Copy, OA, I, E> Copy for Repeated<A, OA, I, E> {}
impl<A: Clone, OA, I, E> Clone for Repeated<A, OA, I, E> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            at_least: self.at_least,
            at_most: self.at_most,
            #[cfg(debug_assertions)]
            location: self.location,
            phantom: EmptyPhantom::new(),
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

    /// Require that the pattern appear exactly the given number of times.
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

impl<'a, I, E, A, OA> ParserSealed<'a, I, (), E> for Repeated<A, OA, I, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
{
    #[inline(always)]
    #[allow(clippy::nonminimal_bool)] // TODO: Remove this, lint is currently buggy
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, ()> {
        if self.at_most == !0 && self.at_least == 0 {
            loop {
                let before = inp.save();
                match self.parser.go::<Check>(inp) {
                    Ok(()) => {}
                    Err(()) => {
                        // TODO: Helper for this? Rewind does this? (seconds one may be bad for other cases)
                        inp.errors.alt = None;
                        inp.rewind(before);
                        break Ok(M::bind(|| ()));
                    }
                }
                #[cfg(debug_assertions)]
                debug_assert!(
                    before.offset() != inp.offset(),
                    "found Repeated combinator making no progress at {}",
                    self.location,
                );
            }
        } else {
            let mut state = self.make_iter::<Check>(inp)?;
            loop {
                #[cfg(debug_assertions)]
                let before = inp.offset();
                match self.next::<Check>(inp, &mut state) {
                    Ok(Some(())) => {}
                    Ok(None) => break Ok(M::bind(|| ())),
                    // TODO: Technically we should be rewinding here: as-is, this is invalid since errorring parsers
                    // are permitted to leave input state unspecified. Really, unwinding should occur *here* and not in
                    // `next`.
                    Err(()) => break Err(()),
                }
                #[cfg(debug_assertions)]
                debug_assert!(
                    before != inp.offset(),
                    "found Repeated combinator making no progress at {}",
                    self.location,
                );
            }
        }
    }

    go_extra!(());
}

impl<'a, A, O, I, E> IterParserSealed<'a, I, O, E> for Repeated<A, O, I, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, O, E>,
{
    type IterState<M: Mode> = usize;

    #[inline(always)]
    fn make_iter<M: Mode>(
        &self,
        _inp: &mut InputRef<'a, '_, I, E>,
    ) -> PResult<Emit, Self::IterState<M>> {
        Ok(0)
    }

    #[inline(always)]
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

impl<'a, A, O, I, E> ConfigIterParserSealed<'a, I, O, E> for Repeated<A, O, I, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, O, E>,
{
    type Config = RepeatedCfg;

    #[inline(always)]
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
pub struct SeparatedBy<A, B, OA, OB, I, E> {
    pub(crate) parser: A,
    pub(crate) separator: B,
    pub(crate) at_least: usize,
    // Slightly evil: Should be `Option<usize>`, but we encode `!0` as 'no cap' because it's so large
    pub(crate) at_most: u64,
    pub(crate) allow_leading: bool,
    pub(crate) allow_trailing: bool,
    #[cfg(debug_assertions)]
    pub(crate) location: Location<'static>,
    #[allow(dead_code)]
    pub(crate) phantom: EmptyPhantom<(OA, OB, E, I)>,
}

impl<A: Copy, B: Copy, OA, OB, I, E> Copy for SeparatedBy<A, B, OA, OB, I, E> {}
impl<A: Clone, B: Clone, OA, OB, I, E> Clone for SeparatedBy<A, B, OA, OB, I, E> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            separator: self.separator.clone(),
            at_least: self.at_least,
            at_most: self.at_most,
            allow_leading: self.allow_leading,
            allow_trailing: self.allow_trailing,
            #[cfg(debug_assertions)]
            location: self.location,
            phantom: EmptyPhantom::new(),
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

    /// Require that the pattern appear exactly the given number of times.
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
    /// let r#enum = text::ascii::keyword::<_, _, _, extra::Err<Simple<char>>>("enum")
    ///     .padded()
    ///     .ignore_then(text::ascii::ident()
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

impl<'a, I, E, A, B, OA, OB> IterParserSealed<'a, I, OA, E> for SeparatedBy<A, B, OA, OB, I, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
    B: Parser<'a, I, OB, E>,
{
    type IterState<M: Mode> = usize
    where
        I: 'a;

    #[inline(always)]
    fn make_iter<M: Mode>(
        &self,
        _inp: &mut InputRef<'a, '_, I, E>,
    ) -> PResult<Emit, Self::IterState<M>> {
        Ok(0)
    }

    #[inline(always)]
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
            if self.separator.go::<Check>(inp).is_err() {
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

impl<'a, I, E, A, B, OA, OB> ParserSealed<'a, I, (), E> for SeparatedBy<A, B, OA, OB, I, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
    B: Parser<'a, I, OB, E>,
{
    #[inline(always)]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, ()> {
        let mut state = self.make_iter::<Check>(inp)?;
        loop {
            #[cfg(debug_assertions)]
            let before = inp.offset();
            match self.next::<Check>(inp, &mut state) {
                Ok(Some(())) => {}
                Ok(None) => break Ok(M::bind(|| ())),
                // TODO: Technically we should be rewinding here: as-is, this is invalid since errorring parsers
                // are permitted to leave input state unspecified. Really, unwinding should occur *here* and not in
                // `next`.
                Err(()) => break Err(()),
            }
            #[cfg(debug_assertions)]
            debug_assert!(
                before != inp.offset(),
                "found SeparatedBy combinator making no progress at {}",
                self.location,
            );
        }
    }

    go_extra!(());
}

/// See [`IterParser::enumerate`].
pub struct Enumerate<A, O> {
    pub(crate) parser: A,
    #[allow(dead_code)]
    pub(crate) phantom: EmptyPhantom<O>,
}

impl<A: Copy, O> Copy for Enumerate<A, O> {}
impl<A: Clone, O> Clone for Enumerate<A, O> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, I, O, E, A> IterParserSealed<'a, I, (usize, O), E> for Enumerate<A, O>
where
    A: IterParser<'a, I, O, E>,
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    type IterState<M: Mode> = (usize, A::IterState<M>)
    where
        I: 'a;

    #[inline(always)]
    fn make_iter<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
    ) -> PResult<Emit, Self::IterState<M>> {
        Ok((0, A::make_iter(&self.parser, inp)?))
    }

    #[inline(always)]
    fn next<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        state: &mut Self::IterState<M>,
    ) -> IPResult<M, (usize, O)> {
        let out = self
            .parser
            .next(inp, &mut state.1)?
            .map(|out| M::map(out, |out| (state.0, out)));
        state.0 += 1;
        Ok(out)
    }
}

/// See [`IterParser::collect`].
pub struct Collect<A, O, C> {
    pub(crate) parser: A,
    #[cfg(debug_assertions)]
    pub(crate) location: Location<'static>,
    #[allow(dead_code)]
    pub(crate) phantom: EmptyPhantom<(O, C)>,
}

impl<A: Copy, O, C> Copy for Collect<A, O, C> {}
impl<A: Clone, O, C> Clone for Collect<A, O, C> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            #[cfg(debug_assertions)]
            location: self.location,
            phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, I, O, E, A, C> ParserSealed<'a, I, C, E> for Collect<A, O, C>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: IterParser<'a, I, O, E>,
    C: Container<O>,
{
    #[inline(always)]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, C> {
        let mut output = M::bind::<C, _>(|| C::default());
        let mut iter_state = self.parser.make_iter::<M>(inp)?;
        #[cfg(debug_assertions)]
        let mut i = 0;
        loop {
            #[cfg(debug_assertions)]
            let before = inp.offset();
            match self.parser.next::<M>(inp, &mut iter_state) {
                Ok(Some(out)) => {
                    M::combine_mut(&mut output, out, |output: &mut C, item| output.push(item));
                }
                Ok(None) => break Ok(output),
                Err(()) => break Err(()),
            }
            // We only check after the second iteration because that's when we *must* have consumed both item
            // and separator.
            #[cfg(debug_assertions)]
            if !A::NONCONSUMPTION_IS_OK {
                if i >= 1 {
                    debug_assert!(
                        before != inp.offset(),
                        "found Collect combinator making no progress at {}",
                        self.location,
                    );
                }
                i += 1;
            }
        }
    }

    go_extra!(C);
}

/// See [`IterParser::collect_exactly`]
pub struct CollectExactly<A, O, C> {
    pub(crate) parser: A,
    #[allow(dead_code)]
    pub(crate) phantom: EmptyPhantom<(O, C)>,
}

impl<A: Copy, O, C> Copy for CollectExactly<A, O, C> {}
impl<A: Clone, O, C> Clone for CollectExactly<A, O, C> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, I, O, E, A, C> ParserSealed<'a, I, C, E> for CollectExactly<A, O, C>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: IterParser<'a, I, O, E>,
    C: ContainerExactly<O>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, C> {
        let before = inp.offset();
        let mut output = M::bind(|| C::uninit());
        let mut iter_state = self.parser.make_iter::<M>(inp)?;
        for idx in 0..C::LEN {
            match self.parser.next::<M>(inp, &mut iter_state) {
                Ok(Some(out)) => {
                    M::combine_mut(&mut output, out, |c, out| C::write(c, idx, out));
                }
                Ok(None) => {
                    inp.add_alt(inp.offset, None, None, inp.span_since(before));
                    // SAFETY: We're guaranteed to have initialized up to `idx` values
                    M::map(output, |mut output| unsafe {
                        C::drop_before(&mut output, idx)
                    });
                    return Err(());
                }
                Err(()) => {
                    // SAFETY: We're guaranteed to have initialized up to `idx` values
                    M::map(output, |mut output| unsafe {
                        C::drop_before(&mut output, idx)
                    });
                    return Err(());
                }
            }
        }
        // SAFETY: If we reach this point, we guarantee to have initialized C::LEN values
        Ok(M::map(output, |output| unsafe { C::take(output) }))
    }

    go_extra!(C);
}

/// See [`Parser::or_not`].
#[derive(Copy, Clone)]
pub struct OrNot<A> {
    pub(crate) parser: A,
}

impl<'a, I, O, E, A> ParserSealed<'a, I, Option<O>, E> for OrNot<A>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, O, E>,
{
    #[inline(always)]
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

impl<'a, A, O, I, E> IterParserSealed<'a, I, O, E> for OrNot<A>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, O, E>,
{
    type IterState<M: Mode> = bool;

    #[inline(always)]
    fn make_iter<M: Mode>(
        &self,
        _inp: &mut InputRef<'a, '_, I, E>,
    ) -> PResult<Emit, Self::IterState<M>> {
        Ok(false)
    }

    #[inline(always)]
    fn next<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        finished: &mut Self::IterState<M>,
    ) -> IPResult<M, O> {
        if *finished {
            return Ok(None);
        }

        let before = inp.save();
        match self.parser.go::<M>(inp) {
            Ok(item) => {
                *finished = true;
                Ok(Some(item))
            }
            Err(()) => {
                inp.rewind(before);
                *finished = true;
                Ok(None)
            }
        }
    }
}

/// See [`Parser::not`].
pub struct Not<A, OA> {
    pub(crate) parser: A,
    #[allow(dead_code)]
    pub(crate) phantom: EmptyPhantom<OA>,
}

impl<A: Copy, OA> Copy for Not<A, OA> {}
impl<A: Clone, OA> Clone for Not<A, OA> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, I, E, A, OA> ParserSealed<'a, I, (), E> for Not<A, OA>
where
    I: ValueInput<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
{
    #[inline(always)]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, ()> {
        let before = inp.save();

        let alt = inp.errors.alt.take();

        let result = self.parser.go::<Check>(inp);
        let result_span = inp.span_since(before.offset());
        inp.rewind(before);

        inp.errors.alt = alt;

        match result {
            Ok(()) => {
                let (at, found) = inp.next_inner();
                inp.add_alt(at, None, found.map(|f| f.into()), result_span);
                Err(())
            }
            Err(()) => Ok(M::bind(|| ())),
        }
    }

    go_extra!(());
}

/// See [`IterParser::flatten`].
#[cfg(feature = "nightly")]
pub struct Flatten<A, O> {
    pub(crate) parser: A,
    #[allow(dead_code)]
    pub(crate) phantom: EmptyPhantom<O>,
}

#[cfg(feature = "nightly")]
impl<A: Copy, O> Copy for Flatten<A, O> {}
#[cfg(feature = "nightly")]
impl<A: Clone, O> Clone for Flatten<A, O> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            phantom: EmptyPhantom::new(),
        }
    }
}

#[cfg(feature = "nightly")]
impl<'a, A, O, I, E> IterParserSealed<'a, I, O::Item, E> for Flatten<A, O>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: IterParser<'a, I, O, E>,
    O: IntoIterator,
{
    type IterState<M: Mode> = (A::IterState<M>, Option<M::Output<O::IntoIter>>);

    #[inline(always)]
    fn make_iter<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
    ) -> PResult<Emit, Self::IterState<M>> {
        Ok((self.parser.make_iter(inp)?, None))
    }

    #[inline(always)]
    fn next<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        (st, iter): &mut Self::IterState<M>,
    ) -> IPResult<M, O::Item> {
        if let Some(item) = iter
            .as_mut()
            .and_then(|i| M::get_or(M::map(M::from_mut(i), |i| i.next()), || None))
        {
            return Ok(Some(M::bind(move || item)));
        }

        // TODO: Debug looping check
        loop {
            let before = inp.save();
            match self.parser.next::<M>(inp, st) {
                Ok(Some(item)) => match M::get_or(
                    M::map(
                        M::from_mut(iter.insert(M::map(item, |i| i.into_iter()))),
                        |i| i.next().map(Some),
                    ),
                    || Some(None),
                ) {
                    Some(Some(item)) => break Ok(Some(M::bind(move || item))),
                    Some(None) => break Ok(Some(M::bind(|| unreachable!()))),
                    None => continue,
                },
                Ok(None) => break Ok(None),
                Err(()) => {
                    inp.rewind(before);
                    break Err(());
                }
            }
        }
    }
}

/// See [`Parser::and_is`].
pub struct AndIs<A, B, OB> {
    pub(crate) parser_a: A,
    pub(crate) parser_b: B,
    #[allow(dead_code)]
    pub(crate) phantom: EmptyPhantom<OB>,
}

impl<A: Copy, B: Copy, OB> Copy for AndIs<A, B, OB> {}
impl<A: Clone, B: Clone, OB> Clone for AndIs<A, B, OB> {
    fn clone(&self) -> Self {
        Self {
            parser_a: self.parser_a.clone(),
            parser_b: self.parser_b.clone(),
            phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, I, E, A, B, OA, OB> ParserSealed<'a, I, OA, E> for AndIs<A, B, OB>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
    B: Parser<'a, I, OB, E>,
{
    #[inline(always)]
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

/// See [`IterParser::foldr`].
pub struct Foldr<F, A, B, OA, E> {
    pub(crate) parser_a: A,
    pub(crate) parser_b: B,
    pub(crate) folder: F,
    #[cfg(debug_assertions)]
    pub(crate) location: Location<'static>,
    #[allow(dead_code)]
    pub(crate) phantom: EmptyPhantom<(OA, E)>,
}

impl<F: Copy, A: Copy, B: Copy, OA, E> Copy for Foldr<F, A, B, OA, E> {}
impl<F: Clone, A: Clone, B: Clone, OA, E> Clone for Foldr<F, A, B, OA, E> {
    fn clone(&self) -> Self {
        Self {
            parser_a: self.parser_a.clone(),
            parser_b: self.parser_b.clone(),
            folder: self.folder.clone(),
            #[cfg(debug_assertions)]
            location: self.location,
            phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, I, F, A, B, O, OA, E> ParserSealed<'a, I, O, E> for Foldr<F, A, B, OA, E>
where
    I: Input<'a>,
    A: IterParser<'a, I, OA, E>,
    B: Parser<'a, I, O, E>,
    E: ParserExtra<'a, I>,
    F: Fn(OA, O) -> O,
{
    #[inline(always)]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O>
    where
        Self: Sized,
    {
        let mut a_out = M::bind(|| Vec::new());
        let mut iter_state = self.parser_a.make_iter::<M>(inp)?;
        loop {
            #[cfg(debug_assertions)]
            let before = inp.offset();
            match self.parser_a.next::<M>(inp, &mut iter_state) {
                Ok(Some(out)) => {
                    M::combine_mut(&mut a_out, out, |a_out, item| a_out.push(item));
                }
                Ok(None) => break,
                Err(()) => return Err(()),
            }
            #[cfg(debug_assertions)]
            if !A::NONCONSUMPTION_IS_OK {
                debug_assert!(
                    before != inp.offset(),
                    "found Foldr combinator making no progress at {}",
                    self.location,
                );
            }
        }

        let b_out = self.parser_b.go::<M>(inp)?;

        Ok(M::combine(a_out, b_out, |a_out, b_out| {
            a_out.into_iter().rfold(b_out, |b, a| (self.folder)(a, b))
        }))
    }

    go_extra!(O);
}

/// See [`IterParser::foldr_with`].
pub struct FoldrWith<F, A, B, OA, E> {
    pub(crate) parser_a: A,
    pub(crate) parser_b: B,
    pub(crate) folder: F,
    #[cfg(debug_assertions)]
    pub(crate) location: Location<'static>,
    #[allow(dead_code)]
    pub(crate) phantom: EmptyPhantom<(OA, E)>,
}

impl<F: Copy, A: Copy, B: Copy, OA, E> Copy for FoldrWith<F, A, B, OA, E> {}
impl<F: Clone, A: Clone, B: Clone, OA, E> Clone for FoldrWith<F, A, B, OA, E> {
    fn clone(&self) -> Self {
        Self {
            parser_a: self.parser_a.clone(),
            parser_b: self.parser_b.clone(),
            folder: self.folder.clone(),
            #[cfg(debug_assertions)]
            location: self.location,
            phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, I, F, A, B, O, OA, E> ParserSealed<'a, I, O, E> for FoldrWith<F, A, B, OA, E>
where
    I: Input<'a>,
    A: IterParser<'a, I, OA, E>,
    B: Parser<'a, I, O, E>,
    E: ParserExtra<'a, I>,
    F: Fn(OA, O, &mut MapExtra<'a, '_, '_, I, E>) -> O,
{
    #[inline(always)]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O>
    where
        Self: Sized,
    {
        let mut a_out = M::bind(Vec::new);
        let mut iter_state = self.parser_a.make_iter::<M>(inp)?;
        loop {
            let before = inp.offset();
            match self.parser_a.next::<M>(inp, &mut iter_state) {
                Ok(Some(out)) => {
                    M::combine_mut(&mut a_out, out, |a_out, item| a_out.push((item, before)));
                }
                Ok(None) => break,
                Err(()) => return Err(()),
            }
            #[cfg(debug_assertions)]
            if !A::NONCONSUMPTION_IS_OK {
                debug_assert!(
                    before != inp.offset(),
                    "found FoldrWithState combinator making no progress at {}",
                    self.location,
                );
            }
        }

        let b_out = self.parser_b.go::<M>(inp)?;

        Ok(M::combine(a_out, b_out, |a_out, b_out| {
            a_out.into_iter().rfold(b_out, |b, (a, before)| {
                (self.folder)(a, b, &mut MapExtra::new(before, inp))
            })
        }))
    }

    go_extra!(O);
}

/// See [`Parser::foldl`].
pub struct Foldl<F, A, B, OB, E> {
    pub(crate) parser_a: A,
    pub(crate) parser_b: B,
    pub(crate) folder: F,
    #[cfg(debug_assertions)]
    pub(crate) location: Location<'static>,
    #[allow(dead_code)]
    pub(crate) phantom: EmptyPhantom<(OB, E)>,
}

impl<F: Copy, A: Copy, B: Copy, OB, E> Copy for Foldl<F, A, B, OB, E> {}
impl<F: Clone, A: Clone, B: Clone, OB, E> Clone for Foldl<F, A, B, OB, E> {
    fn clone(&self) -> Self {
        Self {
            parser_a: self.parser_a.clone(),
            parser_b: self.parser_b.clone(),
            folder: self.folder.clone(),
            #[cfg(debug_assertions)]
            location: self.location,
            phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, I, F, A, B, O, OB, E> ParserSealed<'a, I, O, E> for Foldl<F, A, B, OB, E>
where
    I: Input<'a>,
    A: Parser<'a, I, O, E>,
    B: IterParser<'a, I, OB, E>,
    E: ParserExtra<'a, I>,
    F: Fn(O, OB) -> O,
{
    #[inline(always)]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O>
    where
        Self: Sized,
    {
        let mut out = self.parser_a.go::<M>(inp)?;
        let mut iter_state = self.parser_b.make_iter::<M>(inp)?;
        loop {
            #[cfg(debug_assertions)]
            let before = inp.offset();
            match self.parser_b.next::<M>(inp, &mut iter_state) {
                Ok(Some(b_out)) => {
                    out = M::combine(out, b_out, |out, b_out| (self.folder)(out, b_out));
                }
                Ok(None) => break Ok(out),
                Err(()) => break Err(()),
            }
            #[cfg(debug_assertions)]
            if !B::NONCONSUMPTION_IS_OK {
                debug_assert!(
                    before != inp.offset(),
                    "found Foldl combinator making no progress at {}",
                    self.location,
                );
            }
        }
    }

    go_extra!(O);
}

/// See [`Parser::foldl_with`].
pub struct FoldlWith<F, A, B, OB, E> {
    pub(crate) parser_a: A,
    pub(crate) parser_b: B,
    pub(crate) folder: F,
    #[cfg(debug_assertions)]
    pub(crate) location: Location<'static>,
    #[allow(dead_code)]
    pub(crate) phantom: EmptyPhantom<(OB, E)>,
}

impl<F: Copy, A: Copy, B: Copy, OB, E> Copy for FoldlWith<F, A, B, OB, E> {}
impl<F: Clone, A: Clone, B: Clone, OB, E> Clone for FoldlWith<F, A, B, OB, E> {
    fn clone(&self) -> Self {
        Self {
            parser_a: self.parser_a.clone(),
            parser_b: self.parser_b.clone(),
            folder: self.folder.clone(),
            #[cfg(debug_assertions)]
            location: self.location,
            phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, I, F, A, B, O, OB, E> ParserSealed<'a, I, O, E> for FoldlWith<F, A, B, OB, E>
where
    I: Input<'a>,
    A: Parser<'a, I, O, E>,
    B: IterParser<'a, I, OB, E>,
    E: ParserExtra<'a, I>,
    F: Fn(O, OB, &mut MapExtra<'a, '_, '_, I, E>) -> O,
{
    #[inline(always)]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O>
    where
        Self: Sized,
    {
        let before_all = inp.offset();
        let mut out = self.parser_a.go::<M>(inp)?;
        let mut iter_state = self.parser_b.make_iter::<M>(inp)?;
        loop {
            #[cfg(debug_assertions)]
            let before = inp.offset();
            match self.parser_b.next::<M>(inp, &mut iter_state) {
                Ok(Some(b_out)) => {
                    out = M::combine(out, b_out, |out, b_out| {
                        (self.folder)(out, b_out, &mut MapExtra::new(before_all, inp))
                    })
                }
                Ok(None) => break Ok(out),
                Err(()) => break Err(()),
            }
            #[cfg(debug_assertions)]
            if !B::NONCONSUMPTION_IS_OK {
                debug_assert!(
                    before != inp.offset(),
                    "found FoldlWithState combinator making no progress at {}",
                    self.location,
                );
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

impl<'a, I, O, E, A> ParserSealed<'a, I, O, E> for Rewind<A>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, O, E>,
{
    #[inline(always)]
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

impl<'a, I, O, E, A, F> ParserSealed<'a, I, O, E> for MapErr<A, F>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, O, E>,
    F: Fn(E::Error) -> E::Error,
{
    #[inline(always)]
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

// /// See [`Parser::map_err_with_span`].
// #[derive(Copy, Clone)]
// pub struct MapErrWithSpan<A, F> {
//     pub(crate) parser: A,
//     pub(crate) mapper: F,
// }

// impl<'a, I, O, E, A, F> ParserSealed<'a, I, O, E> for MapErrWithSpan<A, F>
// where
//     I: Input<'a>,
//     E: ParserExtra<'a, I>,
//     A: Parser<'a, I, O, E>,
//     F: Fn(E::Error, I::Span) -> E::Error,
// {
//     #[inline(always)]
//     fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O>
//     where
//         Self: Sized,
//     {
//         let start = inp.offset();
//         let res = self.parser.go::<M>(inp);

//         if res.is_err() {
//             let mut e = inp.errors.alt.take().expect("error but no alt?");
//             let span = inp.span_since(start);
//             e.err = (self.mapper)(e.err, span);
//             inp.errors.alt = Some(e);
//         }

//         res
//     }

//     go_extra!(O);
// }

/// See [`Parser::map_err_with_state`].
#[derive(Copy, Clone)]
pub struct MapErrWithState<A, F> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
}

impl<'a, I, O, E, A, F> ParserSealed<'a, I, O, E> for MapErrWithState<A, F>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, O, E>,
    F: Fn(E::Error, I::Span, &mut E::State) -> E::Error,
{
    #[inline(always)]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O>
    where
        Self: Sized,
    {
        let start = inp.offset();
        let res = self.parser.go::<M>(inp);

        if res.is_err() {
            let mut e = inp.errors.alt.take().expect("error but no alt?");
            let span = inp.span_since(start);
            e.err = (self.mapper)(e.err, span, inp.state());
            inp.errors.alt = Some(e);
        }

        res
    }

    go_extra!(O);
}

/// See [`Parser::validate`]
pub struct Validate<A, OA, F> {
    pub(crate) parser: A,
    pub(crate) validator: F,
    #[allow(dead_code)]
    pub(crate) phantom: EmptyPhantom<OA>,
}

impl<A: Copy, OA, F: Copy> Copy for Validate<A, OA, F> {}
impl<A: Clone, OA, F: Clone> Clone for Validate<A, OA, F> {
    fn clone(&self) -> Self {
        Validate {
            parser: self.parser.clone(),
            validator: self.validator.clone(),
            phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, I, OA, U, E, A, F> ParserSealed<'a, I, U, E> for Validate<A, OA, F>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, OA, E>,
    F: Fn(OA, &mut MapExtra<'a, '_, '_, I, E>, &mut Emitter<E::Error>) -> U,
{
    #[inline(always)]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, U>
    where
        Self: Sized,
    {
        let before = inp.offset();
        let out = self.parser.go::<Emit>(inp)?;

        let mut emitter = Emitter::new();
        let out = (self.validator)(out, &mut MapExtra::new(before, inp), &mut emitter);
        for err in emitter.errors() {
            inp.emit(inp.offset, err);
        }
        Ok(M::bind(|| out))
    }

    go_extra!(U);
}

// /// See [`Parser::or_else`].
// #[derive(Copy, Clone)]
// pub struct OrElse<A, F> {
//     pub(crate) parser: A,
//     pub(crate) or_else: F,
// }

// impl<'a, I, O, E, A, F> ParserSealed<'a, I, O, E> for OrElse<A, F>
// where
//     I: Input<'a>,
//     E: ParserExtra<'a, I>,
//     A: Parser<'a, I, O, E>,
//     F: Fn(E::Error) -> Result<O, E::Error>,
// {
//     #[inline(always)]
//     fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O>
//     where
//         Self: Sized,
//     {
//         let before = inp.save();
//         match self.parser.go::<M>(inp) {
//             Ok(out) => Ok(out),
//             Err(()) => {
//                 let err = inp.errors.alt.take().expect("error but no alt?");
//                 match (self.or_else)(err.err) {
//                     Ok(out) => {
//                         inp.rewind(before);
//                         Ok(M::bind(|| out))
//                     }
//                     Err(new_err) => {
//                         inp.errors.alt = Some(Located {
//                             pos: err.pos,
//                             err: new_err,
//                         });
//                         Err(())
//                     }
//                 }
//             }
//         }
//     }

//     go_extra!(O);
// }

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
