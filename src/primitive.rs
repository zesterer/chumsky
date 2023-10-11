//! Parser primitives that accept specific token patterns.
//!
//! *“These creatures you call mice, you see, they are not quite as they appear. They are merely the protrusion into
//! our dimension of vastly hyperintelligent pandimensional beings.”*
//!
//! Chumsky parsers are created by combining together smaller parsers. Right at the bottom of the pile are the parser
//! primitives, a parser developer's bread & butter. Each of these primitives are very easy to understand in isolation,
//! usually only doing one thing.
//!
//! ## The Important Ones
//!
//! - [`just`]: parses a specific input or sequence of inputs
//! - [`any`]: parses any single input
//! - [`one_of`]: parses any one of a sequence of inputs
//! - [`none_of`]: parses any input that does not appear in a sequence of inputs
//! - [`end`]: parses the end of input (i.e: if there any more inputs, this parse fails)

use super::*;

/// See [`end`].
pub struct End<I, E>(EmptyPhantom<(E, I)>);

/// A parser that accepts only the end of input.
///
/// The output type of this parser is `()`.
pub const fn end<'a, I: Input<'a>, E: ParserExtra<'a, I>>() -> End<I, E> {
    End(EmptyPhantom::new())
}

impl<I, E> Copy for End<I, E> {}
impl<I, E> Clone for End<I, E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, I, E> ParserSealed<'a, I, (), E> for End<I, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, ()> {
        let before = inp.offset();
        match inp.next_maybe_inner() {
            (_, None) => Ok(M::bind(|| ())),
            (at, Some(tok)) => {
                inp.add_alt(at, Some(None), Some(tok.into()), inp.span_since(before));
                Err(())
            }
        }
    }

    go_extra!(());
}

/// See [`empty`].
pub struct Empty<I, E>(EmptyPhantom<(E, I)>);

/// A parser that parses no inputs.
///
/// The output type of this parser is `()`.
pub const fn empty<I, E>() -> Empty<I, E> {
    Empty(EmptyPhantom::new())
}

impl<I, E> Copy for Empty<I, E> {}
impl<I, E> Clone for Empty<I, E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, I, E> ParserSealed<'a, I, (), E> for Empty<I, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    #[inline]
    fn go<M: Mode>(&self, _: &mut InputRef<'a, '_, I, E>) -> PResult<M, ()> {
        Ok(M::bind(|| ()))
    }

    go_extra!(());
}

/// Configuration for [`just`], used in [`ConfigParser::configure`]
pub struct JustCfg<T> {
    seq: Option<T>,
}

impl<T> JustCfg<T> {
    /// Set the sequence to be used while parsing
    #[inline]
    pub fn seq(mut self, new_seq: T) -> Self {
        self.seq = Some(new_seq);
        self
    }
}

impl<T> Default for JustCfg<T> {
    #[inline]
    fn default() -> Self {
        JustCfg { seq: None }
    }
}

/// See [`just`].
pub struct Just<T, I, E = EmptyErr> {
    seq: T,
    #[allow(dead_code)]
    phantom: EmptyPhantom<(E, I)>,
}

impl<T: Copy, I, E> Copy for Just<T, I, E> {}
impl<T: Clone, I, E> Clone for Just<T, I, E> {
    fn clone(&self) -> Self {
        Self {
            seq: self.seq.clone(),
            phantom: EmptyPhantom::new(),
        }
    }
}

/// A parser that accepts only the given input.
///
/// The output type of this parser is `C`, the input or sequence that was provided.
///
/// # Examples
///
/// ```
/// # use chumsky::{prelude::*, error::Simple};
/// let question = just::<_, _, extra::Err<Simple<char>>>('?');
///
/// assert_eq!(question.parse("?").into_result(), Ok('?'));
/// // This fails because '?' was not found
/// assert!(question.parse("!").has_errors());
/// // This fails because the parser expects an end to the input after the '?'
/// assert!(question.parse("?!").has_errors());
/// ```
pub const fn just<'a, T, I, E>(seq: T) -> Just<T, I, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    I::Token: PartialEq,
    T: OrderedSeq<'a, I::Token> + Clone,
{
    Just {
        seq,
        phantom: EmptyPhantom::new(),
    }
}

impl<'a, I, E, T> ParserSealed<'a, I, T, E> for Just<T, I, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    I::Token: PartialEq,
    T: OrderedSeq<'a, I::Token> + Clone,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, T> {
        Self::go_cfg::<M>(self, inp, JustCfg::default())
    }

    go_extra!(T);
}

impl<'a, I, E, T> ConfigParserSealed<'a, I, T, E> for Just<T, I, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    I::Token: PartialEq,
    T: OrderedSeq<'a, I::Token> + Clone,
{
    type Config = JustCfg<T>;

    #[inline]
    fn go_cfg<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        cfg: Self::Config,
    ) -> PResult<M, T> {
        let seq = cfg.seq.as_ref().unwrap_or(&self.seq);

        if let Some(()) = seq.seq_iter().find_map(|next| {
            let before = inp.offset();
            match inp.next_maybe_inner() {
                (_, Some(tok)) if next.borrow() == tok.borrow() => None,
                (at, found) => {
                    inp.add_alt(
                        at,
                        Some(Some(T::to_maybe_ref(next))),
                        found.map(|f| f.into()),
                        inp.span_since(before),
                    );
                    Some(())
                }
            }
        }) {
            Err(())
        } else {
            Ok(M::bind(|| seq.clone()))
        }
    }

    go_cfg_extra!(T);
}

/// See [`one_of`].
pub struct OneOf<T, I, E> {
    seq: T,
    #[allow(dead_code)]
    phantom: EmptyPhantom<(E, I)>,
}

impl<T: Copy, I, E> Copy for OneOf<T, I, E> {}
impl<T: Clone, I, E> Clone for OneOf<T, I, E> {
    fn clone(&self) -> Self {
        Self {
            seq: self.seq.clone(),
            phantom: EmptyPhantom::new(),
        }
    }
}

/// A parser that accepts one of a sequence of specific inputs.
///
/// The output type of this parser is `I`, the input that was found.
///
/// # Examples
///
/// ```
/// # use chumsky::{prelude::*, error::Simple};
/// let digits = one_of::<_, _, extra::Err<Simple<char>>>("0123456789")
///     .repeated()
///     .at_least(1)
///     .collect::<String>();
///
/// assert_eq!(digits.parse("48791").into_result(), Ok("48791".to_string()));
/// assert!(digits.parse("421!53").has_errors());
/// ```
pub const fn one_of<'a, T, I, E>(seq: T) -> OneOf<T, I, E>
where
    I: ValueInput<'a>,
    E: ParserExtra<'a, I>,
    I::Token: PartialEq,
    T: Seq<'a, I::Token>,
{
    OneOf {
        seq,
        phantom: EmptyPhantom::new(),
    }
}

impl<'a, I, E, T> ParserSealed<'a, I, I::Token, E> for OneOf<T, I, E>
where
    I: ValueInput<'a>,
    E: ParserExtra<'a, I>,
    I::Token: PartialEq,
    T: Seq<'a, I::Token>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, I::Token> {
        let before = inp.offset();
        match inp.next_inner() {
            #[allow(suspicious_double_ref_op)] // Is this a clippy bug?
            (_, Some(tok)) if self.seq.contains(tok.borrow()) => Ok(M::bind(|| tok)),
            (at, found) => {
                let err_span = inp.span_since(before);
                inp.add_alt(
                    at,
                    self.seq.seq_iter().map(|e| Some(T::to_maybe_ref(e))),
                    found.map(|f| f.into()),
                    err_span,
                );
                Err(())
            }
        }
    }

    go_extra!(I::Token);
}

/// See [`none_of`].
pub struct NoneOf<T, I, E> {
    seq: T,
    #[allow(dead_code)]
    phantom: EmptyPhantom<(E, I)>,
}

impl<T: Copy, I, E> Copy for NoneOf<T, I, E> {}
impl<T: Clone, I, E> Clone for NoneOf<T, I, E> {
    fn clone(&self) -> Self {
        Self {
            seq: self.seq.clone(),
            phantom: EmptyPhantom::new(),
        }
    }
}

/// A parser that accepts any input that is *not* in a sequence of specific inputs.
///
/// The output type of this parser is `I`, the input that was found.
///
/// # Examples
///
/// ```
/// # use chumsky::{prelude::*, error::Simple};
/// let string = one_of::<_, _, extra::Err<Simple<char>>>("\"'")
///     .ignore_then(none_of("\"'").repeated().collect::<String>())
///     .then_ignore(one_of("\"'"));
///
/// assert_eq!(string.parse("'hello'").into_result(), Ok("hello".to_string()));
/// assert_eq!(string.parse("\"world\"").into_result(), Ok("world".to_string()));
/// assert!(string.parse("\"421!53").has_errors());
/// ```
pub const fn none_of<'a, T, I, E>(seq: T) -> NoneOf<T, I, E>
where
    I: ValueInput<'a>,
    E: ParserExtra<'a, I>,
    I::Token: PartialEq,
    T: Seq<'a, I::Token>,
{
    NoneOf {
        seq,
        phantom: EmptyPhantom::new(),
    }
}

impl<'a, I, E, T> ParserSealed<'a, I, I::Token, E> for NoneOf<T, I, E>
where
    I: ValueInput<'a>,
    E: ParserExtra<'a, I>,
    I::Token: PartialEq,
    T: Seq<'a, I::Token>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, I::Token> {
        let before = inp.offset();
        match inp.next_inner() {
            #[allow(suspicious_double_ref_op)] // Is this a clippy bug?
            (_, Some(tok)) if !self.seq.contains(tok.borrow()) => Ok(M::bind(|| tok)),
            (at, found) => {
                let err_span = inp.span_since(before);
                inp.add_alt(at, None, found.map(|f| f.into()), err_span);
                Err(())
            }
        }
    }

    go_extra!(I::Token);
}

/// See [`custom`].
pub struct Custom<F, I, O, E> {
    f: F,
    #[allow(dead_code)]
    phantom: EmptyPhantom<(E, O, I)>,
}

impl<F: Copy, I, O, E> Copy for Custom<F, I, O, E> {}
impl<F: Clone, I, O, E> Clone for Custom<F, I, O, E> {
    fn clone(&self) -> Self {
        Self {
            f: self.f.clone(),
            phantom: EmptyPhantom::new(),
        }
    }
}

/// TODO
///
/// # Example
///
/// ```
/// # use chumsky::{prelude::*, error::Simple};
///
/// let x = custom::<_, &str, _, extra::Err<Simple<char>>>(|inp| {
///     let _ = inp.next();
///     Ok(())
/// });
///
/// assert_eq!(x.parse("!").into_result(), Ok(()));
/// ```
pub const fn custom<'a, F, I, O, E>(f: F) -> Custom<F, I, O, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    F: Fn(&mut InputRef<'a, '_, I, E>) -> Result<O, E::Error>,
{
    Custom {
        f,
        phantom: EmptyPhantom::new(),
    }
}

impl<'a, I, O, E, F> ParserSealed<'a, I, O, E> for Custom<F, I, O, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    F: Fn(&mut InputRef<'a, '_, I, E>) -> Result<O, E::Error>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        let before = inp.offset();
        match (self.f)(inp) {
            Ok(out) => Ok(M::bind(|| out)),
            Err(err) => {
                inp.add_alt_err(before.offset, err);
                Err(())
            }
        }
    }

    go_extra!(O);
}

/// See [`select!`].
pub struct Select<F, I, O, E> {
    filter: F,
    #[allow(dead_code)]
    phantom: EmptyPhantom<(E, O, I)>,
}

impl<F: Copy, I, O, E> Copy for Select<F, I, O, E> {}
impl<F: Clone, I, O, E> Clone for Select<F, I, O, E> {
    fn clone(&self) -> Self {
        Self {
            filter: self.filter.clone(),
            phantom: EmptyPhantom::new(),
        }
    }
}

/// See [`select!`].
pub const fn select<'a, F, I, O, E>(filter: F) -> Select<F, I, O, E>
where
    I: Input<'a>,
    I::Token: Clone + 'a,
    E: ParserExtra<'a, I>,
    F: Fn(I::Token, &mut MapExtra<'a, '_, I, E>) -> Option<O>,
{
    Select {
        filter,
        phantom: EmptyPhantom::new(),
    }
}

impl<'a, I, O, E, F> ParserSealed<'a, I, O, E> for Select<F, I, O, E>
where
    I: ValueInput<'a>,
    I::Token: Clone + 'a,
    E: ParserExtra<'a, I>,
    F: Fn(I::Token, &mut MapExtra<'a, '_, I, E>) -> Option<O>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        let before = inp.offset();
        let next = inp.next_inner();
        let err_span = inp.span_since(before);
        let (at, found) = match next {
            (at, Some(tok)) => match (self.filter)(tok.clone(), &mut MapExtra::new(before, inp)) {
                Some(out) => return Ok(M::bind(|| out)),
                None => (at, Some(tok.into())),
            },
            (at, found) => (at, found.map(|f| f.into())),
        };
        inp.add_alt(at, None, found, err_span);
        Err(())
    }

    go_extra!(O);
}

/// See [`select_ref!`].
pub struct SelectRef<F, I, O, E> {
    filter: F,
    #[allow(dead_code)]
    phantom: EmptyPhantom<(E, O, I)>,
}

impl<F: Copy, I, O, E> Copy for SelectRef<F, I, O, E> {}
impl<F: Clone, I, O, E> Clone for SelectRef<F, I, O, E> {
    fn clone(&self) -> Self {
        Self {
            filter: self.filter.clone(),
            phantom: EmptyPhantom::new(),
        }
    }
}

/// See [`select_ref!`].
pub const fn select_ref<'a, F, I, O, E>(filter: F) -> SelectRef<F, I, O, E>
where
    I: BorrowInput<'a>,
    I::Token: 'a,
    E: ParserExtra<'a, I>,
    F: Fn(&'a I::Token, &mut MapExtra<'a, '_, I, E>) -> Option<O>,
{
    SelectRef {
        filter,
        phantom: EmptyPhantom::new(),
    }
}

impl<'a, I, O, E, F> ParserSealed<'a, I, O, E> for SelectRef<F, I, O, E>
where
    I: BorrowInput<'a>,
    I::Token: 'a,
    E: ParserExtra<'a, I>,
    F: Fn(&'a I::Token, &mut MapExtra<'a, '_, I, E>) -> Option<O>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        let before = inp.offset();
        let next = inp.next_ref_inner();
        let err_span = inp.span_since(before);
        let (at, found) = match next {
            (at, Some(tok)) => match (self.filter)(tok, &mut MapExtra::new(before, inp)) {
                Some(out) => return Ok(M::bind(|| out)),
                None => (at, Some(tok.into())),
            },
            (at, found) => (at, found.map(|f| f.into())),
        };
        inp.add_alt(at, None, found, err_span);
        Err(())
    }

    go_extra!(O);
}

/// See [`any`].
pub struct Any<I, E> {
    #[allow(dead_code)]
    phantom: EmptyPhantom<(E, I)>,
}

impl<I, E> Copy for Any<I, E> {}
impl<I, E> Clone for Any<I, E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, I, E> ParserSealed<'a, I, I::Token, E> for Any<I, E>
where
    I: ValueInput<'a>,
    E: ParserExtra<'a, I>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, I::Token> {
        let before = inp.offset();
        match inp.next_inner() {
            (_, Some(tok)) => Ok(M::bind(|| tok)),
            (at, found) => {
                let err_span = inp.span_since(before);
                inp.add_alt(at, None, found.map(|f| f.into()), err_span);
                Err(())
            }
        }
    }

    go_extra!(I::Token);
}

/// A parser that accepts any input (but not the end of input).
///
/// The output type of this parser is `I::Token`, the input that was found.
///
/// # Examples
///
/// ```
/// # use chumsky::{prelude::*, error::Simple};
/// let any = any::<_, extra::Err<Simple<char>>>();
///
/// assert_eq!(any.parse("a").into_result(), Ok('a'));
/// assert_eq!(any.parse("7").into_result(), Ok('7'));
/// assert_eq!(any.parse("\t").into_result(), Ok('\t'));
/// assert!(any.parse("").has_errors());
/// ```
pub const fn any<'a, I: Input<'a>, E: ParserExtra<'a, I>>() -> Any<I, E> {
    Any {
        phantom: EmptyPhantom::new(),
    }
}

/// See [`any_ref`].
pub struct AnyRef<I, E> {
    #[allow(dead_code)]
    phantom: EmptyPhantom<(E, I)>,
}

impl<I, E> Copy for AnyRef<I, E> {}
impl<I, E> Clone for AnyRef<I, E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, I, E> ParserSealed<'a, I, &'a I::Token, E> for AnyRef<I, E>
where
    I: BorrowInput<'a>,
    E: ParserExtra<'a, I>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, &'a I::Token> {
        let before = inp.offset();
        match inp.next_ref_inner() {
            (_, Some(tok)) => Ok(M::bind(|| tok)),
            (at, found) => {
                let err_span = inp.span_since(before);
                inp.add_alt(at, None, found.map(|f| f.into()), err_span);
                Err(())
            }
        }
    }

    go_extra!(&'a I::Token);
}

/// A parser that accepts any input (but not the end of input).
///
/// The output type of this parser is `&'a I::Token`, the input that was found.
///
/// This function is the borrowing equivalent of [any]. Where possible, it's recommended to use [any] instead.
///
/// # Examples
///
/// ```
/// # use chumsky::{prelude::*, error::Simple};
/// let any_ref_0 = any_ref::<_, extra::Err<Simple<char>>>();
/// let any_ref_1 = any_ref::<_, extra::Err<Simple<char>>>();
///
/// assert_eq!(any_ref_1.parse(&['a'; 1]).into_result(), Ok(&'a'));
/// assert_eq!(any_ref_1.parse(&['7'; 1]).into_result(), Ok(&'7'));
/// assert_eq!(any_ref_1.parse(&['\t'; 1]).into_result(), Ok(&'\t'));
/// assert!(any_ref_0.parse(&[]).has_errors());
/// ```
pub const fn any_ref<'a, I: BorrowInput<'a>, E: ParserExtra<'a, I>>() -> AnyRef<I, E> {
    AnyRef {
        phantom: EmptyPhantom::new(),
    }
}

/// See [`map_ctx`].
pub struct MapCtx<A, AE, F, E> {
    pub(crate) parser: A,
    pub(crate) mapper: F,
    #[allow(dead_code)]
    pub(crate) phantom: EmptyPhantom<(AE, E)>,
}

impl<A: Copy, AE, F: Copy, E> Copy for MapCtx<A, AE, F, E> {}
impl<A: Clone, AE, F: Clone, E> Clone for MapCtx<A, AE, F, E> {
    fn clone(&self) -> Self {
        MapCtx {
            parser: self.parser.clone(),
            mapper: self.mapper.clone(),
            phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, I, O, E, EI, A, F> ParserSealed<'a, I, O, E> for MapCtx<A, EI, F, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    EI: ParserExtra<'a, I, Error = E::Error, State = E::State>,
    A: Parser<'a, I, O, EI>,
    F: Fn(&E::Context) -> EI::Context,
    EI::Context: 'a,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        inp.with_ctx(&(self.mapper)(inp.ctx()), |inp| self.parser.go::<M>(inp))
    }

    go_extra!(O);
}

/// Apply a mapping function to the context of this parser. Note that this combinator will
/// behave differently from all other maps, in terms of which parsers it effects - while
/// other maps apply to the output of the parser, and thus read left-to-right, this one
/// applies to the _input_ of the parser, and as such applies right-to-left.
///
/// More technically, if all combinators form a 'tree' of parsers, where each node executes
/// its children in turn, normal maps apply up the tree. This means a parent mapper gets the
/// result of its children, applies the map, then passes the new result to its parent. This map,
/// however, applies down the tree. Context is provided from the parent,
/// such as [`Parser::ignore_with_ctx`] and [`Parser::then_with_ctx`],
/// and gets altered before being provided to the children.
///
/// ```
/// # use chumsky::{prelude::*, error::Simple};
///
/// let upper = just::<u8, &[u8], extra::Context<u8>>(b'0').configure(|cfg, ctx: &u8| cfg.seq(*ctx));
///
/// let inc = one_of::<_, _, extra::Default>(b'a'..=b'z')
///     .ignore_with_ctx(map_ctx::<_, u8, &[u8], extra::Context<u8>, extra::Context<u8>, _>(|c: &u8| c.to_ascii_uppercase(), upper))
///     .to_slice()
///     .repeated()
///     .at_least(1)
///     .collect::<Vec<_>>();
///
/// assert_eq!(inc.parse(b"aAbB" as &[_]).into_result(), Ok(vec![b"aA" as &[_], b"bB"]));
/// assert!(inc.parse(b"aB").has_errors());
/// ```
/// You can not only change the value of the context but also change the type entirely:
/// ```
/// # use chumsky::{
///         extra,
///         primitive::{just, map_ctx},
///         ConfigParser, Parser,
/// };
///
/// fn string_ctx<'a>() -> impl Parser<'a, &'a str, (), extra::Context<String>> {
///     just("".to_owned())
///         .configure(|cfg, s: &String| cfg.seq(s.clone()))
///         .ignored()
/// }
///
/// fn usize_ctx<'a>() -> impl Parser<'a, &'a str, (), extra::Context<usize>> {
///     map_ctx::<_, _, _, extra::Context<usize>, extra::Context<String>, _>(
///        |num: &usize| num.to_string(),
///        string_ctx(),
///     )
/// }
///
/// fn specific_usize<'a>(num: usize) -> impl Parser<'a, &'a str, ()> {
///     usize_ctx().with_ctx(num)
/// }
/// assert!(!specific_usize(10).parse("10").has_errors());
/// ```
pub const fn map_ctx<'a, P, OP, I, E, EP, F>(mapper: F, parser: P) -> MapCtx<P, EP, F, E>
where
    F: Fn(&E::Context) -> EP::Context,
    I: Input<'a>,
    P: Parser<'a, I, OP, EP>,
    E: ParserExtra<'a, I>,
    EP: ParserExtra<'a, I>,
    EP::Context: 'a,
{
    MapCtx {
        parser,
        mapper,
        phantom: EmptyPhantom::new(),
    }
}

/// See [`fn@todo`].
pub struct Todo<I, O, E> {
    location: Location<'static>,
    #[allow(dead_code)]
    phantom: EmptyPhantom<(O, E, I)>,
}

impl<I, O, E> Copy for Todo<I, O, E> {}
impl<I, O, E> Clone for Todo<I, O, E> {
    fn clone(&self) -> Self {
        *self
    }
}

/// A parser that can be used wherever you need to implement a parser later.
///
/// This parser is analogous to the [`todo!`] and [`unimplemented!`] macros, but will produce a panic when used to
/// parse input, not immediately when invoked.
///
/// This function is useful when developing your parser, allowing you to prototype and run parts of your parser without
/// committing to implementing the entire thing immediately.
///
/// The output type of this parser is whatever you want it to be: it'll never produce output!
///
/// # Examples
///
/// ```should_panic
/// # use chumsky::prelude::*;
/// let int = just::<_, _, extra::Err<Simple<char>>>("0x").ignore_then(todo())
///     .or(just("0b").ignore_then(text::digits(2).to_slice()))
///     .or(text::int(10).to_slice());
///
/// // Decimal numbers are parsed
/// assert_eq!(int.parse("12").into_result(), Ok("12"));
/// // Binary numbers are parsed
/// assert_eq!(int.parse("0b00101").into_result(), Ok("00101"));
/// // Parsing hexidecimal numbers results in a panic because the parser is unimplemented
/// int.parse("0xd4");
/// ```
#[track_caller]
pub fn todo<'a, I: Input<'a>, O, E: ParserExtra<'a, I>>() -> Todo<I, O, E> {
    Todo {
        location: *Location::caller(),
        phantom: EmptyPhantom::new(),
    }
}

impl<'a, I, O, E> ParserSealed<'a, I, O, E> for Todo<I, O, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    #[inline]
    fn go<M: Mode>(&self, _inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        todo!(
            "Attempted to use an unimplemented parser at {}",
            self.location
        )
    }

    go_extra!(O);
}

/// See [`choice`].
#[derive(Copy, Clone)]
pub struct Choice<T> {
    parsers: T,
}

/// Parse using a tuple of many parsers, producing the output of the first to successfully parse.
///
/// This primitive has a twofold improvement over a chain of [`Parser::or`] calls:
///
/// - Rust's trait solver seems to resolve the [`Parser`] impl for this type much faster, significantly reducing
///   compilation times.
///
/// - Parsing is likely a little faster in some cases because the resulting parser is 'less careful' about error
///   routing, and doesn't perform the same fine-grained error prioritization that [`Parser::or`] does.
///
/// These qualities make this parser ideal for lexers.
///
/// The output type of this parser is the output type of the inner parsers.
///
/// # Examples
///
/// ```
/// # use chumsky::prelude::*;
/// #[derive(Clone, Debug, PartialEq)]
/// enum Token<'a> {
///     If,
///     For,
///     While,
///     Fn,
///     Int(u64),
///     Ident(&'a str),
/// }
///
/// let tokens = choice((
///     text::ascii::keyword::<_, _, _, extra::Err<Simple<char>>>("if").to(Token::If),
///     text::ascii::keyword("for").to(Token::For),
///     text::ascii::keyword("while").to(Token::While),
///     text::ascii::keyword("fn").to(Token::Fn),
///     text::int(10).from_str().unwrapped().map(Token::Int),
///     text::ascii::ident().map(Token::Ident),
/// ))
///     .padded()
///     .repeated()
///     .collect::<Vec<_>>();
///
/// use Token::*;
/// assert_eq!(
///     tokens.parse("if 56 for foo while 42 fn bar").into_result(),
///     Ok(vec![If, Int(56), For, Ident("foo"), While, Int(42), Fn, Ident("bar")]),
/// );
/// ```
pub const fn choice<T>(parsers: T) -> Choice<T> {
    Choice { parsers }
}

macro_rules! impl_choice_for_tuple {
    () => {};
    ($head:ident $($X:ident)*) => {
        impl_choice_for_tuple!($($X)*);
        impl_choice_for_tuple!(~ $head $($X)*);
    };
    (~ $Head:ident $($X:ident)+) => {
        #[allow(unused_variables, non_snake_case)]
        impl<'a, I, E, $Head, $($X),*, O> ParserSealed<'a, I, O, E> for Choice<($Head, $($X,)*)>
        where
            I: Input<'a>,
            E: ParserExtra<'a, I>,
            $Head: Parser<'a, I, O, E>,
            $($X: Parser<'a, I, O, E>),*
        {
            #[inline]
            fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
                let before = inp.save();

                let Choice { parsers: ($Head, $($X,)*), .. } = self;

                match $Head.go::<M>(inp) {
                    Ok(out) => return Ok(out),
                    Err(()) => inp.rewind(before),
                }

                $(
                    match $X.go::<M>(inp) {
                        Ok(out) => return Ok(out),
                        Err(()) => inp.rewind(before),
                    }
                )*

                Err(())
            }

            go_extra!(O);
        }
    };
    (~ $Head:ident) => {
        impl<'a, I, E, $Head, O> ParserSealed<'a, I, O, E> for Choice<($Head,)>
        where
            I: Input<'a>,
            E: ParserExtra<'a, I>,
            $Head:  Parser<'a, I, O, E>,
        {
            #[inline]
            fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
                self.parsers.0.go::<M>(inp)
            }

            go_extra!(O);
        }
    };
}

impl_choice_for_tuple!(A_ B_ C_ D_ E_ F_ G_ H_ I_ J_ K_ L_ M_ N_ O_ P_ Q_ R_ S_ T_ U_ V_ W_ X_ Y_ Z_);

impl<'a, 'b, A, I, O, E> ParserSealed<'a, I, O, E> for Choice<&'b [A]>
where
    A: Parser<'a, I, O, E>,
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        if self.parsers.is_empty() {
            let offs = inp.offset();
            let err_span = inp.span_since(offs);
            inp.add_alt(offs.offset, None, None, err_span);
            Err(())
        } else {
            let before = inp.save();
            match self.parsers.iter().find_map(|parser| {
                inp.rewind(before);
                match parser.go::<M>(inp) {
                    Ok(out) => Some(out),
                    Err(()) => None,
                }
            }) {
                Some(out) => Ok(out),
                None => Err(()),
            }
        }
    }

    go_extra!(O);
}

impl<'a, A, I, O, E> ParserSealed<'a, I, O, E> for Choice<Vec<A>>
where
    A: Parser<'a, I, O, E>,
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        choice(&self.parsers[..]).go::<M>(inp)
    }
    go_extra!(O);
}

impl<'a, A, I, O, E, const N: usize> ParserSealed<'a, I, O, E> for Choice<[A; N]>
where
    A: Parser<'a, I, O, E>,
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        choice(&self.parsers[..]).go::<M>(inp)
    }
    go_extra!(O);
}

/// See [`group`].
#[derive(Copy, Clone)]
pub struct Group<T> {
    parsers: T,
}

/// Parse using a tuple of many parsers, producing a tuple of outputs if all successfully parse,
/// otherwise returning an error if any parsers fail.
///
/// This parser is to [`Parser::then`] as [`choice`] is to [`Parser::or`]
pub const fn group<T>(parsers: T) -> Group<T> {
    Group { parsers }
}

impl<'a, I, O, E, P, const N: usize> ParserSealed<'a, I, [O; N], E> for Group<[P; N]>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    P: Parser<'a, I, O, E>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, [O; N]> {
        let mut arr: [MaybeUninit<_>; N] = MaybeUninitExt::uninit_array();
        self.parsers
            .iter()
            .zip(arr.iter_mut())
            .try_for_each(|(p, res)| {
                res.write(p.go::<M>(inp)?);
                Ok(())
            })?;
        // SAFETY: We guarantee that all parers succeeded and as such all items have been initialized
        //         if we reach this point
        Ok(M::array(unsafe { MaybeUninitExt::array_assume_init(arr) }))
    }

    go_extra!([O; N]);
}

macro_rules! flatten_map {
    // map a single element into a 1-tuple
    (<$M:ident> $head:ident) => {
        $M::map(
            $head,
            |$head| ($head,),
        )
    };
    // combine two elements into a 2-tuple
    (<$M:ident> $head1:ident $head2:ident) => {
        $M::combine(
            $head1,
            $head2,
            |$head1, $head2| ($head1, $head2),
        )
    };
    // combine and flatten n-tuples from recursion
    (<$M:ident> $head:ident $($X:ident)+) => {
        $M::combine(
            $head,
            flatten_map!(
                <$M>
                $($X)+
            ),
            |$head, ($($X),+)| ($head, $($X),+),
        )
    };
}

macro_rules! impl_group_for_tuple {
    () => {};
    ($head:ident $ohead:ident $($X:ident $O:ident)*) => {
        impl_group_for_tuple!($($X $O)*);
        impl_group_for_tuple!(~ $head $ohead $($X $O)*);
    };
    (~ $($X:ident $O:ident)*) => {
        #[allow(unused_variables, non_snake_case)]
        impl<'a, I, E, $($X),*, $($O),*> ParserSealed<'a, I, ($($O,)*), E> for Group<($($X,)*)>
        where
            I: Input<'a>,
            E: ParserExtra<'a, I>,
            $($X: Parser<'a, I, $O, E>),*
        {
            #[inline]
            fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, ($($O,)*)> {
                let Group { parsers: ($($X,)*) } = self;

                $(
                    let $X = $X.go::<M>(inp)?;
                )*

                Ok(flatten_map!(<M> $($X)*))
            }

            go_extra!(($($O,)*));
        }
    };
}

impl_group_for_tuple! {
    A_ OA
    B_ OB
    C_ OC
    D_ OD
    E_ OE
    F_ OF
    G_ OG
    H_ OH
    I_ OI
    J_ OJ
    K_ OK
    L_ OL
    M_ OM
    N_ ON
    O_ OO
    P_ OP
    Q_ OQ
    R_ OR
    S_ OS
    T_ OT
    U_ OU
    V_ OV
    W_ OW
    X_ OX
    Y_ OY
    Z_ OZ
}
