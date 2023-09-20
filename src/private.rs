use super::*;

#[derive(Clone)]
pub(crate) struct Located<T, E> {
    pub(crate) pos: T,
    pub(crate) err: E,
}

impl<T, E> Located<T, E> {
    #[inline]
    pub fn at(pos: T, err: E) -> Self {
        Self { pos, err }
    }
}

/// The result of calling [`Parser::go`]
pub(crate) type PResult<M, O> = Result<<M as Mode>::Output<O>, ()>;
/// The result of calling [`IterParser::next`]
pub(crate) type IPResult<M, O> = Result<Option<<M as Mode>::Output<O>>, ()>;

/// An abstract parse mode - can be [`Emit`] or [`Check`] in practice, and represents the
/// common interface for handling both in the same method.
pub trait Mode {
    /// The output of this mode for a given type
    type Output<T>;

    /// Bind the result of a closure into an output
    fn bind<T, F: FnOnce() -> T>(f: F) -> Self::Output<T>;

    /// Given an [`Output`](Self::Output), takes its value and return a newly generated output
    fn map<T, U, F: FnOnce(T) -> U>(x: Self::Output<T>, f: F) -> Self::Output<U>;

    /// Choose between two fallible functions to execute depending on the mode.
    fn choose<A, T, E, F: FnOnce(A) -> Result<T, E>, G: FnOnce(A) -> Result<(), E>>(
        arg: A,
        f: F,
        g: G,
    ) -> Result<Self::Output<T>, E>;

    /// Given two [`Output`](Self::Output)s, take their values and combine them into a new
    /// output value
    fn combine<T, U, V, F: FnOnce(T, U) -> V>(
        x: Self::Output<T>,
        y: Self::Output<U>,
        f: F,
    ) -> Self::Output<V>;
    /// By-reference version of [`Mode::combine`].
    fn combine_mut<T, U, F: FnOnce(&mut T, U)>(x: &mut Self::Output<T>, y: Self::Output<U>, f: F);

    /// Given an array of outputs, bind them into an output of arrays
    fn array<T, const N: usize>(x: [Self::Output<T>; N]) -> Self::Output<[T; N]>;

    /// Invoke a parser user the current mode. This is normally equivalent to
    /// [`parser.go::<M>(inp)`](Parser::go), but it can be called on unsized values such as
    /// `dyn Parser`.
    fn invoke<'a, I, O, E, P>(parser: &P, inp: &mut InputRef<'a, '_, I, E>) -> PResult<Self, O>
    where
        I: Input<'a>,
        E: ParserExtra<'a, I>,
        P: Parser<'a, I, O, E> + ?Sized;

    /// Invoke a parser with configuration using the current mode. This is normally equivalent
    /// to [`parser.go::<M>(inp)`](ConfigParser::go_cfg), but it can be called on unsized values
    /// such as `dyn Parser`.
    fn invoke_cfg<'a, I, O, E, P>(
        parser: &P,
        inp: &mut InputRef<'a, '_, I, E>,
        cfg: P::Config,
    ) -> PResult<Self, O>
    where
        I: Input<'a>,
        E: ParserExtra<'a, I>,
        P: ConfigParser<'a, I, O, E> + ?Sized;
}

/// Emit mode - generates parser output
pub struct Emit;

impl Mode for Emit {
    type Output<T> = T;
    #[inline(always)]
    fn bind<T, F: FnOnce() -> T>(f: F) -> Self::Output<T> {
        f()
    }
    #[inline(always)]
    fn map<T, U, F: FnOnce(T) -> U>(x: Self::Output<T>, f: F) -> Self::Output<U> {
        f(x)
    }
    #[inline(always)]
    fn choose<A, T, E, F: FnOnce(A) -> Result<T, E>, G: FnOnce(A) -> Result<(), E>>(
        arg: A,
        f: F,
        _: G,
    ) -> Result<Self::Output<T>, E> {
        f(arg)
    }
    #[inline(always)]
    fn combine<T, U, V, F: FnOnce(T, U) -> V>(
        x: Self::Output<T>,
        y: Self::Output<U>,
        f: F,
    ) -> Self::Output<V> {
        f(x, y)
    }
    #[inline(always)]
    fn combine_mut<T, U, F: FnOnce(&mut T, U)>(x: &mut Self::Output<T>, y: Self::Output<U>, f: F) {
        f(x, y)
    }
    #[inline(always)]
    fn array<T, const N: usize>(x: [Self::Output<T>; N]) -> Self::Output<[T; N]> {
        x
    }

    #[inline(always)]
    fn invoke<'a, I, O, E, P>(parser: &P, inp: &mut InputRef<'a, '_, I, E>) -> PResult<Self, O>
    where
        I: Input<'a>,
        E: ParserExtra<'a, I>,
        P: Parser<'a, I, O, E> + ?Sized,
    {
        parser.go_emit(inp)
    }

    #[inline(always)]
    fn invoke_cfg<'a, I, O, E, P>(
        parser: &P,
        inp: &mut InputRef<'a, '_, I, E>,
        cfg: P::Config,
    ) -> PResult<Self, O>
    where
        I: Input<'a>,
        E: ParserExtra<'a, I>,
        P: ConfigParser<'a, I, O, E> + ?Sized,
    {
        parser.go_emit_cfg(inp, cfg)
    }
}

/// Check mode - all output is discarded, and only uses parsers to check validity
pub struct Check;

impl Mode for Check {
    type Output<T> = ();
    #[inline(always)]
    fn bind<T, F: FnOnce() -> T>(_: F) -> Self::Output<T> {}
    #[inline(always)]
    fn map<T, U, F: FnOnce(T) -> U>(_: Self::Output<T>, _: F) -> Self::Output<U> {}
    #[inline(always)]
    fn choose<A, T, E, F: FnOnce(A) -> Result<T, E>, G: FnOnce(A) -> Result<(), E>>(
        arg: A,
        _: F,
        g: G,
    ) -> Result<Self::Output<T>, E> {
        g(arg)
    }
    #[inline(always)]
    fn combine<T, U, V, F: FnOnce(T, U) -> V>(
        _: Self::Output<T>,
        _: Self::Output<U>,
        _: F,
    ) -> Self::Output<V> {
    }
    #[inline(always)]
    fn combine_mut<T, U, F: FnOnce(&mut T, U)>(_: &mut Self::Output<T>, _: Self::Output<U>, _: F) {}
    #[inline(always)]
    fn array<T, const N: usize>(_: [Self::Output<T>; N]) -> Self::Output<[T; N]> {}

    #[inline(always)]
    fn invoke<'a, I, O, E, P>(parser: &P, inp: &mut InputRef<'a, '_, I, E>) -> PResult<Self, O>
    where
        I: Input<'a>,
        E: ParserExtra<'a, I>,
        P: Parser<'a, I, O, E> + ?Sized,
    {
        parser.go_check(inp)
    }

    #[inline(always)]
    fn invoke_cfg<'a, I, O, E, P>(
        parser: &P,
        inp: &mut InputRef<'a, '_, I, E>,
        cfg: P::Config,
    ) -> PResult<Self, O>
    where
        I: Input<'a>,
        E: ParserExtra<'a, I>,
        P: ConfigParser<'a, I, O, E> + ?Sized,
    {
        parser.go_check_cfg(inp, cfg)
    }
}

// TODO: Consider removing these sealed traits in favour of `Sealed`, with the given methods just being on `Parser`
// with doc(hidden)

pub trait ParserSealed<'a, I: Input<'a>, O, E: ParserExtra<'a, I>> {
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O>
    where
        Self: Sized;

    fn go_emit(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<Emit, O>;
    fn go_check(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<Check, O>;

    fn boxed<'b>(self) -> Boxed<'a, 'b, I, O, E>
    where
        Self: MaybeSync + Sized + 'a + 'b,
    {
        Boxed {
            inner: RefC::new(self),
        }
    }
}

pub trait ConfigParserSealed<'a, I, O, E>: ParserSealed<'a, I, O, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    type Config: Default;

    fn go_cfg<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>, cfg: Self::Config) -> PResult<M, O>
    where
        Self: Sized;

    fn go_emit_cfg(&self, inp: &mut InputRef<'a, '_, I, E>, cfg: Self::Config) -> PResult<Emit, O>;
    fn go_check_cfg(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        cfg: Self::Config,
    ) -> PResult<Check, O>;
}

pub trait IterParserSealed<'a, I, O, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    type IterState<M: Mode>
    where
        I: 'a;

    // Determines whether this iter parser is expected to not consume input on each iteration
    const NONCONSUMPTION_IS_OK: bool = false;

    #[doc(hidden)]
    fn make_iter<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
    ) -> PResult<Emit, Self::IterState<M>>;
    #[doc(hidden)]
    fn next<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        state: &mut Self::IterState<M>,
    ) -> IPResult<M, O>;
}

pub trait ConfigIterParserSealed<'a, I, O, E>: IterParserSealed<'a, I, O, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    type Config: Default;

    #[doc(hidden)]
    fn next_cfg<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        state: &mut Self::IterState<M>,
        cfg: &Self::Config,
    ) -> IPResult<M, O>;
}

// TODO: Remove this when MaybeUninit transforms to/from arrays stabilize in any form
pub(crate) trait MaybeUninitExt<T>: Sized {
    /// Identical to the unstable [`MaybeUninit::uninit_array`]
    fn uninit_array<const N: usize>() -> [Self; N];

    /// Identical to the unstable [`MaybeUninit::array_assume_init`]
    unsafe fn array_assume_init<const N: usize>(uninit: [Self; N]) -> [T; N];
}

impl<T> MaybeUninitExt<T> for MaybeUninit<T> {
    #[allow(clippy::uninit_assumed_init)]
    fn uninit_array<const N: usize>() -> [Self; N] {
        // SAFETY: Output type is entirely uninhabited - IE, it's made up entirely of `MaybeUninit`
        unsafe { MaybeUninit::uninit().assume_init() }
    }

    unsafe fn array_assume_init<const N: usize>(uninit: [Self; N]) -> [T; N] {
        (&uninit as *const [Self; N] as *const [T; N]).read()
    }
}

pub trait Sealed {}
