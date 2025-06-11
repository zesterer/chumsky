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

    fn from_mut<T>(r: &mut Self::Output<T>) -> Self::Output<&mut T>;

    fn get_or<T, F: FnOnce() -> T>(r: Self::Output<T>, f: F) -> T;

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

    #[cfg(feature = "pratt")]
    fn invoke_pratt_op_prefix<'src, 'parse, Op, I, O, E>(
        op: &Op,
        inp: &mut InputRef<'src, 'parse, I, E>,
        pre_expr: &input::Checkpoint<'src, 'parse, I, <E::State as Inspector<'src, I>>::Checkpoint>,
        f: &impl Fn(&mut InputRef<'src, 'parse, I, E>, i32) -> PResult<Self, O>,
    ) -> pratt::OperatorResult<Self::Output<O>, ()>
    where
        Op: pratt::Operator<'src, I, O, E>,
        I: Input<'src>,
        E: ParserExtra<'src, I>;
    #[cfg(feature = "pratt")]
    fn invoke_pratt_op_postfix<'src, 'parse, Op, I, O, E>(
        op: &Op,
        inp: &mut InputRef<'src, 'parse, I, E>,
        pre_expr: &input::Cursor<'src, 'parse, I>,
        pre_op: &input::Checkpoint<'src, 'parse, I, <E::State as Inspector<'src, I>>::Checkpoint>,
        lhs: Self::Output<O>,
        min_power: i32,
    ) -> pratt::OperatorResult<Self::Output<O>, Self::Output<O>>
    where
        Op: pratt::Operator<'src, I, O, E>,
        I: Input<'src>,
        E: ParserExtra<'src, I>;
    #[cfg(feature = "pratt")]
    fn invoke_pratt_op_infix<'src, 'parse, Op, I, O, E>(
        op: &Op,
        inp: &mut InputRef<'src, 'parse, I, E>,
        pre_expr: &input::Cursor<'src, 'parse, I>,
        pre_op: &input::Checkpoint<'src, 'parse, I, <E::State as Inspector<'src, I>>::Checkpoint>,
        lhs: Self::Output<O>,
        min_power: i32,
        f: &impl Fn(&mut InputRef<'src, 'parse, I, E>, i32) -> PResult<Self, O>,
    ) -> pratt::OperatorResult<Self::Output<O>, Self::Output<O>>
    where
        Op: pratt::Operator<'src, I, O, E>,
        I: Input<'src>,
        E: ParserExtra<'src, I>;
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
    fn from_mut<T>(r: &mut Self::Output<T>) -> Self::Output<&mut T> {
        r
    }
    #[inline(always)]
    fn get_or<T, F: FnOnce() -> T>(r: Self::Output<T>, _f: F) -> T {
        r
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

    #[cfg(feature = "pratt")]
    #[inline(always)]
    fn invoke_pratt_op_prefix<'src, 'parse, Op, I, O, E>(
        op: &Op,
        inp: &mut InputRef<'src, 'parse, I, E>,
        pre_expr: &input::Checkpoint<'src, 'parse, I, <E::State as Inspector<'src, I>>::Checkpoint>,
        f: &impl Fn(&mut InputRef<'src, 'parse, I, E>, i32) -> PResult<Self, O>,
    ) -> pratt::OperatorResult<Self::Output<O>, ()>
    where
        Op: pratt::Operator<'src, I, O, E>,
        I: Input<'src>,
        E: ParserExtra<'src, I>,
    {
        op.do_parse_prefix_emit(inp, pre_expr, &f)
    }
    #[cfg(feature = "pratt")]
    #[inline(always)]
    fn invoke_pratt_op_postfix<'src, 'parse, Op, I, O, E>(
        op: &Op,
        inp: &mut InputRef<'src, 'parse, I, E>,
        pre_expr: &input::Cursor<'src, 'parse, I>,
        pre_op: &input::Checkpoint<'src, 'parse, I, <E::State as Inspector<'src, I>>::Checkpoint>,
        lhs: Self::Output<O>,
        min_power: i32,
    ) -> pratt::OperatorResult<Self::Output<O>, Self::Output<O>>
    where
        Op: pratt::Operator<'src, I, O, E>,
        I: Input<'src>,
        E: ParserExtra<'src, I>,
    {
        op.do_parse_postfix_emit(inp, pre_expr, pre_op, lhs, min_power)
    }
    #[cfg(feature = "pratt")]
    #[inline(always)]
    fn invoke_pratt_op_infix<'src, 'parse, Op, I, O, E>(
        op: &Op,
        inp: &mut InputRef<'src, 'parse, I, E>,
        pre_expr: &input::Cursor<'src, 'parse, I>,
        pre_op: &input::Checkpoint<'src, 'parse, I, <E::State as Inspector<'src, I>>::Checkpoint>,
        lhs: Self::Output<O>,
        min_power: i32,
        f: &impl Fn(&mut InputRef<'src, 'parse, I, E>, i32) -> PResult<Self, O>,
    ) -> pratt::OperatorResult<Self::Output<O>, Self::Output<O>>
    where
        Op: pratt::Operator<'src, I, O, E>,
        I: Input<'src>,
        E: ParserExtra<'src, I>,
    {
        op.do_parse_infix_emit(inp, pre_expr, pre_op, lhs, min_power, &f)
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
    fn from_mut<T>(_r: &mut Self::Output<T>) -> Self::Output<&mut T> {}
    #[inline(always)]
    fn get_or<T, F: FnOnce() -> T>(_r: Self::Output<T>, f: F) -> T {
        f()
    }

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

    #[cfg(feature = "pratt")]
    #[inline(always)]
    fn invoke_pratt_op_prefix<'src, 'parse, Op, I, O, E>(
        op: &Op,
        inp: &mut InputRef<'src, 'parse, I, E>,
        pre_expr: &input::Checkpoint<'src, 'parse, I, <E::State as Inspector<'src, I>>::Checkpoint>,
        f: &impl Fn(&mut InputRef<'src, 'parse, I, E>, i32) -> PResult<Self, O>,
    ) -> pratt::OperatorResult<Self::Output<O>, ()>
    where
        Op: pratt::Operator<'src, I, O, E>,
        I: Input<'src>,
        E: ParserExtra<'src, I>,
    {
        op.do_parse_prefix_check(inp, pre_expr, &f)
    }
    #[cfg(feature = "pratt")]
    #[inline(always)]
    fn invoke_pratt_op_postfix<'src, 'parse, Op, I, O, E>(
        op: &Op,
        inp: &mut InputRef<'src, 'parse, I, E>,
        pre_expr: &input::Cursor<'src, 'parse, I>,
        pre_op: &input::Checkpoint<'src, 'parse, I, <E::State as Inspector<'src, I>>::Checkpoint>,
        lhs: Self::Output<O>,
        min_power: i32,
    ) -> pratt::OperatorResult<Self::Output<O>, Self::Output<O>>
    where
        Op: pratt::Operator<'src, I, O, E>,
        I: Input<'src>,
        E: ParserExtra<'src, I>,
    {
        op.do_parse_postfix_check(inp, pre_expr, pre_op, lhs, min_power)
    }
    #[cfg(feature = "pratt")]
    #[inline(always)]
    fn invoke_pratt_op_infix<'src, 'parse, Op, I, O, E>(
        op: &Op,
        inp: &mut InputRef<'src, 'parse, I, E>,
        pre_expr: &input::Cursor<'src, 'parse, I>,
        pre_op: &input::Checkpoint<'src, 'parse, I, <E::State as Inspector<'src, I>>::Checkpoint>,
        lhs: Self::Output<O>,
        min_power: i32,
        f: &impl Fn(&mut InputRef<'src, 'parse, I, E>, i32) -> PResult<Self, O>,
    ) -> pratt::OperatorResult<Self::Output<O>, Self::Output<O>>
    where
        Op: pratt::Operator<'src, I, O, E>,
        I: Input<'src>,
        E: ParserExtra<'src, I>,
    {
        op.do_parse_infix_check(inp, pre_expr, pre_op, lhs, min_power, &f)
    }
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
