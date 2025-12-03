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
pub const fn end<'src, I: Input<'src>, E: ParserExtra<'src, I>>() -> End<I, E> {
    End(EmptyPhantom::new())
}

impl<I, E> Copy for End<I, E> {}
impl<I, E> Clone for End<I, E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'src, I, E> Parser<'src, I, (), E> for End<I, E>
where
    I: Input<'src>,
    E: ParserExtra<'src, I>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'src, '_, I, E>) -> PResult<M, ()> {
        let before = inp.save();
        match inp.next_maybe_inner() {
            None => Ok(M::bind(|| ())),
            Some(tok) => {
                let span = inp.span_since(before.cursor());
                inp.rewind(before);
                inp.add_alt([DefaultExpected::EndOfInput], Some(tok.into()), span);
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

impl<'src, I, E> Parser<'src, I, (), E> for Empty<I, E>
where
    I: Input<'src>,
    E: ParserExtra<'src, I>,
{
    #[inline]
    fn go<M: Mode>(&self, _: &mut InputRef<'src, '_, I, E>) -> PResult<M, ()> {
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
/// The output type of this parser is `T`, the input or sequence that was provided.
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
pub const fn just<'src, T, I, E>(seq: T) -> Just<T, I, E>
where
    I: Input<'src>,
    E: ParserExtra<'src, I>,
    I::Token: PartialEq,
    T: OrderedSeq<'src, I::Token> + Clone,
{
    Just {
        seq,
        phantom: EmptyPhantom::new(),
    }
}

impl<'src, I, E, T> Parser<'src, I, T, E> for Just<T, I, E>
where
    I: Input<'src>,
    E: ParserExtra<'src, I>,
    I::Token: PartialEq,
    T: OrderedSeq<'src, I::Token> + Clone,
{
    #[doc(hidden)]
    #[cfg(feature = "debug")]
    fn node_info(&self, scope: &mut debug::NodeScope) -> debug::NodeInfo {
        debug::NodeInfo::Just(self.seq.seq_info(scope))
    }

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'src, '_, I, E>) -> PResult<M, T> {
        Self::go_cfg::<M>(self, inp, JustCfg::default())
    }

    go_extra!(T);
}

impl<'src, I, E, T> ConfigParser<'src, I, T, E> for Just<T, I, E>
where
    I: Input<'src>,
    E: ParserExtra<'src, I>,
    I::Token: PartialEq,
    T: OrderedSeq<'src, I::Token> + Clone,
{
    type Config = JustCfg<T>;

    #[inline]
    fn go_cfg<M: Mode>(
        &self,
        inp: &mut InputRef<'src, '_, I, E>,
        cfg: Self::Config,
    ) -> PResult<M, T> {
        let seq = cfg.seq.as_ref().unwrap_or(&self.seq);
        for next in seq.seq_iter() {
            let before = inp.save();
            match inp.next_maybe_inner() {
                Some(tok) if next.borrow() == tok.borrow() => {}
                found => {
                    let span = inp.span_since(before.cursor());
                    inp.rewind(before);
                    inp.add_alt(
                        [DefaultExpected::Token(T::to_maybe_ref(next))],
                        found.map(|f| f.into()),
                        span,
                    );
                    return Err(());
                }
            }
        }

        Ok(M::bind(|| seq.clone()))
    }
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
pub const fn one_of<'src, T, I, E>(seq: T) -> OneOf<T, I, E>
where
    I: ValueInput<'src>,
    E: ParserExtra<'src, I>,
    I::Token: PartialEq,
    T: Seq<'src, I::Token>,
{
    OneOf {
        seq,
        phantom: EmptyPhantom::new(),
    }
}

impl<'src, I, E, T> Parser<'src, I, I::Token, E> for OneOf<T, I, E>
where
    I: ValueInput<'src>,
    E: ParserExtra<'src, I>,
    I::Token: PartialEq,
    T: Seq<'src, I::Token>,
{
    #[doc(hidden)]
    #[cfg(feature = "debug")]
    fn node_info(&self, scope: &mut debug::NodeScope) -> debug::NodeInfo {
        debug::NodeInfo::OneOf(self.seq.seq_info(scope))
    }

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'src, '_, I, E>) -> PResult<M, I::Token> {
        let before = inp.save();
        match inp.next_inner() {
            #[allow(suspicious_double_ref_op)] // Is this a clippy bug?
            Some(tok) if self.seq.contains(tok.borrow()) => Ok(M::bind(|| tok)),
            found => {
                let err_span = inp.span_since(before.cursor());
                inp.rewind(before);
                inp.add_alt(
                    self.seq
                        .seq_iter()
                        .map(|e| DefaultExpected::Token(T::to_maybe_ref(e))),
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
pub const fn none_of<'src, T, I, E>(seq: T) -> NoneOf<T, I, E>
where
    I: ValueInput<'src>,
    E: ParserExtra<'src, I>,
    I::Token: PartialEq,
    T: Seq<'src, I::Token>,
{
    NoneOf {
        seq,
        phantom: EmptyPhantom::new(),
    }
}

impl<'src, I, E, T> Parser<'src, I, I::Token, E> for NoneOf<T, I, E>
where
    I: ValueInput<'src>,
    E: ParserExtra<'src, I>,
    I::Token: PartialEq,
    T: Seq<'src, I::Token>,
{
    #[doc(hidden)]
    #[cfg(feature = "debug")]
    fn node_info(&self, scope: &mut debug::NodeScope) -> debug::NodeInfo {
        debug::NodeInfo::NoneOf(self.seq.seq_info(scope))
    }

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'src, '_, I, E>) -> PResult<M, I::Token> {
        let before = inp.save();
        match inp.next_inner() {
            // #[allow(suspicious_double_ref_op)] // Is this a clippy bug?
            Some(tok) if !self.seq.contains(tok.borrow()) => Ok(M::bind(|| tok)),
            found => {
                let err_span = inp.span_since(before.cursor());
                inp.rewind(before);
                inp.add_alt(
                    [DefaultExpected::SomethingElse],
                    found.map(|f| f.into()),
                    err_span,
                );
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

/// Declare a parser that uses custom imperative parsing logic.
///
/// This is useful when a particular parser is difficult or impossible to express with chumsky's built-in combinators
/// alone. For example, custom context-sensitive logic can often be implemented using a custom parser and then
/// integrated seamlessly into a more 'vanilla' chumsky parser.
///
/// See the [`InputRef`] docs for information about what operations custom parsers can perform.
///
/// If you are building a library of custom parsers, it is recommended to make use of the [`extension`] API.
///
/// # Example
///
/// ```
/// # use chumsky::{prelude::*, error::{Simple, LabelError}};
///
/// let question = custom::<_, &str, _, extra::Err<Simple<char>>>(|inp| {
///     let before = inp.cursor();
///     match inp.next() {
///         Some('?') => Ok(()),
///         found => Err(Simple::new(found.map(Into::into), inp.span_since(&before))),
///     }
/// });
///
/// assert_eq!(question.parse("?").into_result(), Ok(()));
/// assert!(question.parse("!").has_errors());
/// ```
pub const fn custom<'src, F, I, O, E>(f: F) -> Custom<F, I, O, E>
where
    I: Input<'src>,
    E: ParserExtra<'src, I>,
    F: Fn(&mut InputRef<'src, '_, I, E>) -> Result<O, E::Error>,
{
    Custom {
        f,
        phantom: EmptyPhantom::new(),
    }
}

impl<'src, I, O, E, F> Parser<'src, I, O, E> for Custom<F, I, O, E>
where
    I: Input<'src>,
    E: ParserExtra<'src, I>,
    F: Fn(&mut InputRef<'src, '_, I, E>) -> Result<O, E::Error>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'src, '_, I, E>) -> PResult<M, O> {
        let before = inp.cursor();
        match (self.f)(inp) {
            Ok(out) => Ok(M::bind(|| out)),
            Err(err) => {
                inp.add_alt_err(&before.inner, err);
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
pub const fn select<'src, F, I, O, E>(filter: F) -> Select<F, I, O, E>
where
    I: Input<'src>,
    I::Token: Clone + 'src,
    E: ParserExtra<'src, I>,
    F: Fn(I::Token, &mut MapExtra<'src, '_, I, E>) -> Option<O>,
{
    Select {
        filter,
        phantom: EmptyPhantom::new(),
    }
}

impl<'src, I, O, E, F> Parser<'src, I, O, E> for Select<F, I, O, E>
where
    I: Input<'src>,
    I::Token: Clone + 'src,
    E: ParserExtra<'src, I>,
    F: Fn(I::Token, &mut MapExtra<'src, '_, I, E>) -> Option<O>,
{
    #[doc(hidden)]
    #[cfg(feature = "debug")]
    fn node_info(&self, _scope: &mut debug::NodeScope) -> debug::NodeInfo {
        debug::NodeInfo::Filter(Box::new(debug::NodeInfo::Any))
    }

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'src, '_, I, E>) -> PResult<M, O> {
        let before = inp.save();
        let next = inp.next_maybe_inner();
        let found = match next {
            Some(tok) => {
                match (self.filter)(
                    tok.borrow().clone(),
                    &mut MapExtra::new(before.cursor(), inp),
                ) {
                    Some(out) => return Ok(M::bind(|| out)),
                    None => Some(tok.into()),
                }
            }
            found => found.map(|f| f.into()),
        };
        let err_span = inp.span_since(before.cursor());
        inp.rewind(before);
        inp.add_alt([DefaultExpected::SomethingElse], found, err_span);
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
pub const fn select_ref<'src, F, I, O, E>(filter: F) -> SelectRef<F, I, O, E>
where
    I: BorrowInput<'src>,
    I::Token: 'src,
    E: ParserExtra<'src, I>,
    F: Fn(&'src I::Token, &mut MapExtra<'src, '_, I, E>) -> Option<O>,
{
    SelectRef {
        filter,
        phantom: EmptyPhantom::new(),
    }
}

impl<'src, I, O, E, F> Parser<'src, I, O, E> for SelectRef<F, I, O, E>
where
    I: BorrowInput<'src>,
    I::Token: 'src,
    E: ParserExtra<'src, I>,
    F: Fn(&'src I::Token, &mut MapExtra<'src, '_, I, E>) -> Option<O>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'src, '_, I, E>) -> PResult<M, O> {
        let before = inp.save();
        let next = inp.next_ref_inner();
        let found = match next {
            Some(tok) => match (self.filter)(tok, &mut MapExtra::new(before.cursor(), inp)) {
                Some(out) => return Ok(M::bind(|| out)),
                None => Some(tok.into()),
            },
            found => found.map(|f| f.into()),
        };
        let err_span = inp.span_since(before.cursor());
        inp.rewind(before);
        inp.add_alt([DefaultExpected::SomethingElse], found, err_span);
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

impl<'src, I, E> Parser<'src, I, I::Token, E> for Any<I, E>
where
    I: ValueInput<'src>,
    E: ParserExtra<'src, I>,
{
    #[doc(hidden)]
    #[cfg(feature = "debug")]
    fn node_info(&self, _scope: &mut debug::NodeScope) -> debug::NodeInfo {
        debug::NodeInfo::Any
    }

    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'src, '_, I, E>) -> PResult<M, I::Token> {
        let before = inp.save();
        match inp.next_inner() {
            Some(tok) => Ok(M::bind(|| tok)),
            found => {
                let err_span = inp.span_since(before.cursor());
                inp.rewind(before);
                inp.add_alt([DefaultExpected::Any], found.map(|f| f.into()), err_span);
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
pub const fn any<'src, I: Input<'src>, E: ParserExtra<'src, I>>() -> Any<I, E> {
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

impl<'src, I, E> Parser<'src, I, &'src I::Token, E> for AnyRef<I, E>
where
    I: BorrowInput<'src>,
    E: ParserExtra<'src, I>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'src, '_, I, E>) -> PResult<M, &'src I::Token> {
        let before = inp.save();
        match inp.next_ref_inner() {
            Some(tok) => Ok(M::bind(|| tok)),
            found => {
                let err_span = inp.span_since(before.cursor());
                inp.rewind(before);
                inp.add_alt([DefaultExpected::Any], found.map(|f| f.into()), err_span);
                Err(())
            }
        }
    }

    go_extra!(&'src I::Token);
}

/// A parser that accepts any input (but not the end of input).
///
/// The output type of this parser is `&'src I::Token`, the input that was found.
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
pub const fn any_ref<'src, I: BorrowInput<'src>, E: ParserExtra<'src, I>>() -> AnyRef<I, E> {
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

impl<'src, I, O, E, EI, A, F> Parser<'src, I, O, E> for MapCtx<A, EI, F, E>
where
    I: Input<'src>,
    E: ParserExtra<'src, I>,
    EI: ParserExtra<'src, I, Error = E::Error, State = E::State>,
    A: Parser<'src, I, O, EI>,
    F: Fn(&E::Context) -> EI::Context,
    EI::Context: 'src,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'src, '_, I, E>) -> PResult<M, O> {
        inp.with_ctx(&(self.mapper)(inp.ctx()), |inp| self.parser.go::<M>(inp))
    }

    go_extra!(O);
}

/// Apply a mapping function to the context of this parser.
///
/// Note that this combinator will behave differently from all other maps, in terms of which
/// parsers it effects - while other maps apply to the output of the parser, and thus read left-to-right, this one
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
/// fn string_ctx<'src>() -> impl Parser<'src, &'src str, (), extra::Context<String>> {
///     just("".to_owned())
///         .configure(|cfg, s: &String| cfg.seq(s.clone()))
///         .ignored()
/// }
///
/// fn usize_ctx<'src>() -> impl Parser<'src, &'src str, (), extra::Context<usize>> {
///     map_ctx::<_, _, _, extra::Context<usize>, extra::Context<String>, _>(
///        |num: &usize| num.to_string(),
///        string_ctx(),
///     )
/// }
///
/// fn specific_usize<'src>(num: usize) -> impl Parser<'src, &'src str, ()> {
///     usize_ctx().with_ctx(num)
/// }
/// assert!(!specific_usize(10).parse("10").has_errors());
/// ```
pub const fn map_ctx<'src, P, OP, I, E, EP, F>(mapper: F, parser: P) -> MapCtx<P, EP, F, E>
where
    F: Fn(&E::Context) -> EP::Context,
    I: Input<'src>,
    P: Parser<'src, I, OP, EP>,
    E: ParserExtra<'src, I>,
    EP: ParserExtra<'src, I>,
    EP::Context: 'src,
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
pub fn todo<'src, I: Input<'src>, O, E: ParserExtra<'src, I>>() -> Todo<I, O, E> {
    Todo {
        location: *Location::caller(),
        phantom: EmptyPhantom::new(),
    }
}

impl<'src, I, O, E> Parser<'src, I, O, E> for Todo<I, O, E>
where
    I: Input<'src>,
    E: ParserExtra<'src, I>,
{
    #[inline]
    fn go<M: Mode>(&self, _inp: &mut InputRef<'src, '_, I, E>) -> PResult<M, O> {
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
/// enum Token<'src> {
///     If,
///     For,
///     While,
///     Fn,
///     Int(u64),
///     Ident(&'src str),
/// }
///
/// let tokens = choice((
///     text::ascii::keyword::<_, _, extra::Err<Simple<char>>>("if").to(Token::If),
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
        impl<'src, I, E, $Head, $($X),*, O> Parser<'src, I, O, E> for Choice<($Head, $($X,)*)>
        where
            I: Input<'src>,
            E: ParserExtra<'src, I>,
            $Head: Parser<'src, I, O, E>,
            $($X: Parser<'src, I, O, E>),*
        {
            #[doc(hidden)]
            #[cfg(feature = "debug")]
            fn node_info(&self, scope: &mut debug::NodeScope) -> debug::NodeInfo {
                let Choice { parsers: ($Head, $($X,)*), .. } = self;
                debug::NodeInfo::Choice(vec![$Head.node_info(scope), $($X.node_info(scope)),*])
            }

            #[inline]
            fn go<M: Mode>(&self, inp: &mut InputRef<'src, '_, I, E>) -> PResult<M, O> {
                let before = inp.save();

                let Choice { parsers: ($Head, $($X,)*), .. } = self;

                match $Head.go::<M>(inp) {
                    Ok(out) => return Ok(out),
                    Err(()) => inp.rewind(before.clone()),
                }

                $(
                    match $X.go::<M>(inp) {
                        Ok(out) => return Ok(out),
                        Err(()) => inp.rewind(before.clone()),
                    }
                )*

                Err(())
            }

            go_extra!(O);
        }
    };
    (~ $Head:ident) => {
        impl<'src, I, E, $Head, O> Parser<'src, I, O, E> for Choice<($Head,)>
        where
            I: Input<'src>,
            E: ParserExtra<'src, I>,
            $Head:  Parser<'src, I, O, E>,
        {
            #[inline]
            fn go<M: Mode>(&self, inp: &mut InputRef<'src, '_, I, E>) -> PResult<M, O> {
                self.parsers.0.go::<M>(inp)
            }

            go_extra!(O);
        }
    };
}

impl_choice_for_tuple!(A_ B_ C_ D_ E_ F_ G_ H_ I_ J_ K_ L_ M_ N_ O_ P_ Q_ R_ S_ T_ U_ V_ W_ X_ Y_ Z_);

impl<'src, A, I, O, E> Parser<'src, I, O, E> for Choice<&[A]>
where
    A: Parser<'src, I, O, E>,
    I: Input<'src>,
    E: ParserExtra<'src, I>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'src, '_, I, E>) -> PResult<M, O> {
        if self.parsers.is_empty() {
            let offs = inp.cursor();
            let err_span = inp.span_since(&offs);
            inp.add_alt([], None, err_span);
            Err(())
        } else {
            let before = inp.save();
            for parser in self.parsers.iter() {
                inp.rewind(before.clone());
                if let Ok(out) = parser.go::<M>(inp) {
                    return Ok(out);
                }
            }
            Err(())
        }
    }

    go_extra!(O);
}

impl<'src, A, I, O, E> Parser<'src, I, O, E> for Choice<Vec<A>>
where
    A: Parser<'src, I, O, E>,
    I: Input<'src>,
    E: ParserExtra<'src, I>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'src, '_, I, E>) -> PResult<M, O> {
        choice(&self.parsers[..]).go::<M>(inp)
    }
    go_extra!(O);
}

impl<'src, A, I, O, E, const N: usize> Parser<'src, I, O, E> for Choice<[A; N]>
where
    A: Parser<'src, I, O, E>,
    I: Input<'src>,
    E: ParserExtra<'src, I>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'src, '_, I, E>) -> PResult<M, O> {
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

impl<'src, I, O, E, P, const N: usize> Parser<'src, I, [O; N], E> for Group<[P; N]>
where
    I: Input<'src>,
    E: ParserExtra<'src, I>,
    P: Parser<'src, I, O, E>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'src, '_, I, E>) -> PResult<M, [O; N]> {
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
        impl<'src, I, E, $($X),*, $($O),*> Parser<'src, I, ($($O,)*), E> for Group<($($X,)*)>
        where
            I: Input<'src>,
            E: ParserExtra<'src, I>,
            $($X: Parser<'src, I, $O, E>),*
        {
            #[inline]
            fn go<M: Mode>(&self, inp: &mut InputRef<'src, '_, I, E>) -> PResult<M, ($($O,)*)> {
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

/// See [`set`].
#[derive(Copy, Clone)]
pub struct Set<T> {
    parsers: T,
}

/// Parse using a tuple of parsers in any order, producing the output of the parser set in the provided order.
///
/// The output type of this parser is a tuple of the output types of the inner parsers.
///
/// All parsers must successfully parse.
///
/// Parsers are always tried in the provided order, which means that most specific parsers must be
/// provided first or they might never match. In other words, if two parsers match the same item,
/// the `set`'s input must containt this item twice for the `set` to be successful.
///
/// Be careful! This combinator is O(n^2), which means that in the worst case you could slow down parsing with
/// a lot of parser calls. The worst case happens when all items are present but in the reverse
/// order compared to the list of parsers. To mitigate this you should order your parsers in the
/// same order input usually happens. And you should avoid having too many parsers in the set.
///
/// Parsers that match without making progress (like `empty()` or `something.or_not()`) are applied
/// last to make sure they have no better alternative.
///
/// This means that you can make a parser optional by adding a call to `.or_not()` to it.
///
/// # Examples
///
/// ```
/// # use chumsky::prelude::*;
/// let options = set((
///     just::<_, _, extra::Err<Simple<char>>>("apple\n"),
///     just("banana\n"),
///     just("carrot\n").or_not(),
/// ));
///
/// assert_eq!(
///     options.parse("banana\napple\n").into_result(),
///     Ok(("apple\n", "banana\n", None)),
/// );
/// ```
pub const fn set<T>(parsers: T) -> Set<T> {
    Set { parsers }
}

fn go_or_finish<'src, O, I, E, P, M>(
    item: &mut Option<M::Output<O>>,
    parser: &P,
    inp: &mut InputRef<'src, '_, I, E>,
) -> PResult<M, ()>
where
    I: Input<'src>,
    E: ParserExtra<'src, I>,
    P: Parser<'src, I, O, E>,
    M: Mode,
{
    if item.is_none() {
        match parser.go::<M>(inp) {
            Ok(out) => {
                *item = Some(out);
            }
            Err(()) => {
                return Err(());
            }
        }
    }
    Ok(M::bind(|| ()))
}

fn go_or_rewind<'src, O, I, E, P, M>(
    item: &mut Option<M::Output<O>>,
    parser: &P,
    inp: &mut InputRef<'src, '_, I, E>,
) where
    I: Input<'src>,
    E: ParserExtra<'src, I>,
    P: Parser<'src, I, O, E>,
    M: Mode,
{
    if item.is_none() {
        let save_before = inp.save();
        let pos_before = inp.cursor();
        match parser.go::<M>(inp) {
            Ok(out) => {
                if pos_before == inp.cursor() {
                    inp.rewind(save_before.clone());
                } else {
                    *item = Some(out);
                }
            }
            Err(()) => inp.rewind(save_before.clone()),
        }
    }
}

macro_rules! impl_set_for_tuple {
    () => {};
    ($head_1:ident $head_2:ident $head_3:ident $($X:ident)*) => {
        impl_set_for_tuple!($($X)*);
        impl_set_for_tuple!(~ $head_1 $head_2 $head_3 $($X)*);
    };
    (~ $($O:ident $P:ident $I:ident)+) => {
        #[allow(unused_variables, non_snake_case)]
        impl<'src, I, E, $($P),*, $($O,)*> Parser<'src, I, ($($O,)*), E> for Set<($($P,)*)>
        where
            I: Input<'src>,
            E: ParserExtra<'src, I>,
            $($P: Parser<'src, I, $O, E>),*
        {
            #[inline]
            fn go<M: Mode>(&self, inp: &mut InputRef<'src, '_, I, E>) -> PResult<M, ($($O,)*)> {
                let Set { parsers: ($($P,)*), .. } = self;
                $( let mut $I: Option<M::Output<$O>> = None; )*

                // first iterate until there are no progress
                loop {
                    let start = inp.cursor();
                    $( go_or_rewind::<_, _, _, _, M>(&mut $I, $P, inp); )*
                    // none matched during this loop
                    if start == inp.cursor() {
                        break;
                    }
                }

                // Then a final iteration that matches remaining empty parsers
                $( go_or_finish::<_, _, _, _, M>(&mut $I, $P, inp)?; )*

                // unwrap is ok since we matched all items in the set exactly once
                $( let $I = $I.unwrap(); )*
                Ok(flatten_map!(<M> $($I)*))
            }

            go_extra!(($($O,)*));
        }
    };
}

impl_set_for_tuple!(A1 A2 A3 B1 B2 B3 C1 C2 C3 D1 D2 D3 E1 E2 E3 F1 F2 F3 G1 G2 G3 H1 H2 H3 I1 I2 I3 J1 J2 J3 K1 K2 K3 L1 L2 L3 M1 M2 M3 N1 N2 N3 O1 O2 O3 P1 P2 P3 Q1 Q2 Q3 R1 R2 R3 S1 S2 S3 T1 T2 T3 U1 U2 U3 V1 V2 V3 W1 W2 W3 X1 X2 X3 Y1 Y2 Y3 Z1 Z2 Z3);

impl<'src, P, I, O, E> Parser<'src, I, Vec<O>, E> for Set<Vec<P>>
where
    P: Parser<'src, I, O, E>,
    I: Input<'src>,
    E: ParserExtra<'src, I>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'src, '_, I, E>) -> PResult<M, Vec<O>> {
        let mut tmp = self
            .parsers
            .iter()
            .map(|_| None)
            .collect::<Vec<Option<M::Output<O>>>>();

        // first iterate until there are no progress
        loop {
            let start = inp.cursor();
            for (i, parser) in self.parsers.iter().enumerate() {
                go_or_rewind::<_, _, _, _, M>(&mut tmp[i], parser, inp);
            }
            // none matched during this loop
            if start == inp.cursor() {
                break;
            }
        }

        // Then a final iteration that matches remaining empty parsers
        for (i, parser) in self.parsers.iter().enumerate() {
            go_or_finish::<_, _, _, _, M>(&mut tmp[i], parser, inp)?;
        }

        // unwrap is ok since we matched all items in the se
        let mut result = M::bind(|| Vec::new());
        tmp.into_iter()
            .for_each(|x| M::combine_mut(&mut result, x.unwrap(), |result, x| result.push(x)));
        Ok(result)
    }

    go_extra!(Vec<O>);
}

impl<'src, P, I, O, E, const N: usize> Parser<'src, I, [O; N], E> for Set<[P; N]>
where
    P: Parser<'src, I, O, E>,
    I: Input<'src>,
    E: ParserExtra<'src, I>,
    // remove this requirement when MSRV > 1.80
    O: Copy,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'src, '_, I, E>) -> PResult<M, [O; N]> {
        // Replace this when MRSV > 1.80
        //let mut tmp: [Option<M::Output<O>>; N] = [ const { None }; N];
        let mut tmp: [Option<O>; N] = [None; N];

        // first iterate until there are no progress
        loop {
            let start = inp.cursor();
            for (i, parser) in self.parsers.iter().enumerate() {
                // Replace this when MRSV > 1.80
                //go_or_rewind::<_, _, _, _, M>(&mut tmp[i], parser, inp);
                go_or_rewind::<_, _, _, _, Emit>(&mut tmp[i], parser, inp);
            }
            // none matched during this loop
            if start == inp.cursor() {
                break;
            }
        }

        // Then a final iteration that matches remaining empty parsers
        for (i, parser) in self.parsers.iter().enumerate() {
            // Replace this when MRSV > 1.80
            //go_or_finish::<_, _, _, _, M>(&mut tmp[i], parser, inp)?;
            go_or_finish::<_, _, _, _, Emit>(&mut tmp[i], parser, inp)?;
        }

        // unwrap is ok since we matched all items in the se
        // Replace this when MRSV > 1.80
        //Ok(M::array( tmp.map(|x| x.unwrap()) ))
        Ok(M::bind(|| tmp.map(|x| x.unwrap())))
    }

    go_extra!([O; N]);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn set_parser() {
        fn just(s: &str) -> Just<&str, &str, extra::Err<EmptyErr>> {
            super::just(s)
        }

        // test ordering
        let parser = set((just("abc"), just("def"), just("ijk")));
        assert_eq!(
            parser.parse("ijkdefabc").into_result(),
            Ok(("abc", "def", "ijk")),
        );
        assert_eq!(
            parser.parse("abcdefijk").into_result(),
            Ok(("abc", "def", "ijk")),
        );

        // test inclusion
        let parser = set((choice((just("abc"), just("def"))), just("abc")));
        assert_eq!(parser.parse("defabc").into_result(), Ok(("def", "abc")),);
        let parser = set((choice((just("abc"), just("def"))), just("abc")));
        assert!(parser.parse("abcdef").into_result().is_err());

        // test optionals
        let parser = set((
            just("abc").or_not(),
            just("def").or_not(),
            just("ijk").or_not(),
        ));
        assert_eq!(
            parser.parse("ijkdefabc").into_result(),
            Ok((Some("abc"), Some("def"), Some("ijk"))),
        );
        assert_eq!(
            parser.parse("ijkabc").into_result(),
            Ok((Some("abc"), None, Some("ijk"))),
        );
        assert_eq!(parser.parse("").into_result(), Ok((None, None, None)),);

        // test types
        let parser = set(vec![just("abc"), just("def"), just("ijk")]);
        assert_eq!(
            parser.parse("ijkdefabc").into_result(),
            Ok(vec!["abc", "def", "ijk"]),
        );
        let parser = set([just("abc"), just("def"), just("ijk")]);
        assert_eq!(
            parser.parse("ijkdefabc").into_result(),
            Ok(["abc", "def", "ijk"]),
        );
    }
}
