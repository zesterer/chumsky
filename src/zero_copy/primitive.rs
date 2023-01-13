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
//! - [`filter`]: parses a single input, if the given filter function returns `true`
//! - [`end`]: parses the end of input (i.e: if there any more inputs, this parse fails)

use super::*;

/// See [`end`].
pub struct End<In: ?Sized, Err, State>(PhantomData<(Err, State, In)>);

/// A parser that accepts only the end of input.
///
/// This parser is very useful when you wish to force a parser to consume *all* of the input. It is typically combined
/// with [`Parser::then_ignore`].
///
/// The output type of this parser is `()`.
///
/// # Examples
///
/// ```
/// # use chumsky::zero_copy::prelude::*;
/// assert_eq!(end::<_, Simple<str>, ()>().parse("").into_result(), Ok(()));
/// assert!(end::<_, Simple<str>, ()>().parse("hello").has_errors());
/// ```
///
/// ```
/// # use chumsky::zero_copy::prelude::*;
/// let digits = text::digits::<_, _, Simple<str>, ()>(10);
///
/// // This parser parses digits!
/// assert_eq!(digits.parse("1234").into_result(), Ok("1234"));
///
/// // However, parsers are lazy and do not consume trailing input.
/// // This can be inconvenient if we want to validate all of the input.
/// assert_eq!(digits.parse("1234AhasjADSJAlaDJKSDAK").into_result(), Ok("1234"));
///
/// // To fix this problem, we require that the end of input follows any successfully parsed input
/// let only_digits = digits.then_ignore(end());
///
/// // Now our parser correctly produces an error if any trailing input is found...
/// assert!(only_digits.parse("1234AhasjADSJAlaDJKSDAK").has_errors());
/// // ...while still behaving correctly for inputs that only consist of valid patterns
/// assert_eq!(only_digits.parse("1234").into_result(), Ok("1234"));
/// ```
pub const fn end<'a, In: Input + ?Sized, Err: Error<In>, State: 'a>() -> End<In, Err, State> {
    End(PhantomData)
}

impl<In: ?Sized, Err, State> Copy for End<In, Err, State> {}
impl<In: ?Sized, Err, State> Clone for End<In, Err, State> {
    fn clone(&self) -> Self {
        End(PhantomData)
    }
}

impl<'a, In, Err, State, Ctx> Parser<'a, In, (), Err, State, Ctx> for End<In, Err, State>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, (), Err> {
        let before = inp.save();
        match inp.next() {
            (_, None) => Ok(M::bind(|| ())),
            (at, Some(tok)) => Err(Located::at(
                at,
                Err::expected_found(None, Some(tok), inp.span_since(before)),
            )),
        }
    }

    go_extra!(());
}

/// See [`empty`].
pub struct Empty<In: ?Sized>(PhantomData<In>);

/// A parser that parses no inputs.
///
/// The output type of this parser is `()`.
pub const fn empty<In: Input + ?Sized>() -> Empty<In> {
    Empty(PhantomData)
}

impl<In: ?Sized> Copy for Empty<In> {}
impl<In: ?Sized> Clone for Empty<In> {
    fn clone(&self) -> Self {
        Empty(PhantomData)
    }
}

impl<'a, In, Err, State, Ctx> Parser<'a, In, (), Err, State, Ctx> for Empty<In>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
{
    type Config = ();

    fn go<M: Mode>(&self, _: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, (), Err> {
        Ok(M::bind(|| ()))
    }

    go_extra!(());
}

// impl<'b, T, C: Container<T>> Container<T> for &'b C {
//     type Iter<'a> = C::Iter<'a>;
//     fn iter(&self) -> Self::Iter<'_> { (*self).iter() }
// }

/// See [`just`].
pub struct Just<T, In: ?Sized, Err = EmptyErr, State = (), Ctx = ()> {
    seq: T,
    phantom: PhantomData<(Err, State, Ctx, In)>,
}

impl<T: Copy, In: ?Sized, Err, State, Ctx> Copy for Just<T, In, Err, State, Ctx> {}
impl<T: Clone, In: ?Sized, Err, State, Ctx> Clone for Just<T, In, Err, State, Ctx> {
    fn clone(&self) -> Self {
        Self {
            seq: self.seq.clone(),
            phantom: PhantomData,
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
/// # use chumsky::zero_copy::{prelude::*, error::Simple};
/// let question = just('?').error::<Simple<str>>();
///
/// assert_eq!(question.parse("?").into_result(), Ok('?'));
/// assert!(question.parse("!").has_errors());
/// // This works because parsers do not eagerly consume input, so the '!' is not parsed
/// assert_eq!(question.parse("?!").into_result(), Ok('?'));
/// // This fails because the parser expects an end to the input after the '?'
/// assert!(question.then(end()).parse("?!").has_errors());
/// ```
pub const fn just<T, In, Err, State, Ctx>(seq: T) -> Just<T, In, Err, State, Ctx>
where
    In: Input + ?Sized,
    Err: Error<In>,
    In::Token: PartialEq,
    T: OrderedSeq<In::Token> + Clone,
{
    Just {
        seq,
        phantom: PhantomData,
    }
}

impl<'a, In, Err, State, Ctx, T> Parser<'a, In, T, Err, State, Ctx> for Just<T, In, Err, State, Ctx>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
    In::Token: Clone + PartialEq,
    T: OrderedSeq<In::Token> + Clone,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, T, Err> {
        let mut items = self.seq.seq_iter();
        loop {
            match items.next() {
                Some(next) => {
                    let next = next.borrow();
                    let before = inp.save();
                    match inp.next() {
                        (_, Some(tok)) if *next == tok => {}
                        (at, tok) => {
                            break Err(Located::at(
                                at,
                                Err::expected_found(Some(Some(In::Token::clone(next))), tok, inp.span_since(before)),
                            ))
                        }
                    }
                }
                None => break Ok(M::bind(|| self.seq.clone())),
            }
        }
    }

    go_extra!(T);
}

/// See [`one_of`].
pub struct OneOf<T, In: ?Sized, Err = EmptyErr, State = (), Ctx = ()> {
    seq: T,
    phantom: PhantomData<(Err, State, Ctx, In)>,
}

impl<T: Copy, In: ?Sized, Err, State, Ctx> Copy for OneOf<T, In, Err, State, Ctx> {}
impl<T: Clone, In: ?Sized, Err, State, Ctx> Clone for OneOf<T, In, Err, State, Ctx> {
    fn clone(&self) -> Self {
        Self {
            seq: self.seq.clone(),
            phantom: PhantomData,
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
/// # use chumsky::zero_copy::{prelude::*, error::Simple};
/// let digits = one_of::<_, _, Simple<str>, ()>("0123456789")
///     .repeated()
///     .at_least(1)
///     .collect::<String>()
///     .then_ignore(end());
///
/// assert_eq!(digits.parse("48791").into_result(), Ok("48791".to_string()));
/// assert!(digits.parse("421!53").has_errors());
/// ```
pub const fn one_of<T, In, Err, State>(seq: T) -> OneOf<T, In, Err, State>
where
    In: Input + ?Sized,
    Err: Error<In>,
    In::Token: Clone + PartialEq,
    T: Seq<In::Token>,
{
    OneOf {
        seq,
        phantom: PhantomData,
    }
}

impl<'a, In, Err, State, Ctx, T> Parser<'a, In, In::Token, Err, State, Ctx> for OneOf<T, In, Err, State>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
    In::Token: Clone + PartialEq,
    T: Seq<In::Token>,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, In::Token, Err> {
        let before = inp.save();
        match inp.next() {
            (_, Some(tok)) if self.seq.contains(&tok) => Ok(M::bind(|| tok)),
            (at, found) => Err(Located::at(
                at,
                Err::expected_found(self.seq.seq_iter().map(|not| Some(not.borrow().clone())), found, inp.span_since(before)),
            )),
        }
    }

    go_extra!(In::Token);
}

/// See [`none_of`].
pub struct NoneOf<T, In: ?Sized, Err = EmptyErr, State = (), Ctx = ()> {
    seq: T,
    phantom: PhantomData<(Err, State, Ctx, In)>,
}

impl<T: Copy, In: ?Sized, Err, State, Ctx> Copy for NoneOf<T, In, Err, State, Ctx> {}
impl<T: Clone, In: ?Sized, Err, State, Ctx> Clone for NoneOf<T, In, Err, State, Ctx> {
    fn clone(&self) -> Self {
        Self {
            seq: self.seq.clone(),
            phantom: PhantomData,
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
/// # use chumsky::zero_copy::{prelude::*, error::Simple};
/// let string = one_of::<_, _, Simple<str>, ()>("\"'")
///     .ignore_then(none_of("\"'").repeated().collect::<String>())
///     .then_ignore(one_of("\"'"))
///     .then_ignore(end());
///
/// assert_eq!(string.parse("'hello'").into_result(), Ok("hello".to_string()));
/// assert_eq!(string.parse("\"world\"").into_result(), Ok("world".to_string()));
/// assert!(string.parse("\"421!53").has_errors());
/// ```
pub const fn none_of<T, In, Err, State>(seq: T) -> NoneOf<T, In, Err, State>
where
    In: Input + ?Sized,
    Err: Error<In>,
    In::Token: PartialEq,
    T: Seq<In::Token>,
{
    NoneOf {
        seq,
        phantom: PhantomData,
    }
}

impl<'a, In, Err, State, Ctx, T> Parser<'a, In, In::Token, Err, State, Ctx> for NoneOf<T, In, Err, State>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
    In::Token: PartialEq,
    T: Seq<In::Token>,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, In::Token, Err> {
        let before = inp.save();
        match inp.next() {
            (_, Some(tok)) if !self.seq.contains(&tok) => Ok(M::bind(|| tok)),
            (at, found) => Err(Located::at(
                at,
                Err::expected_found(None, found, inp.span_since(before)),
            )),
        }
    }

    go_extra!(In::Token);
}

/// See [`any`].
pub struct Any<In: ?Sized, Err, State = (), Ctx = ()> {
    phantom: PhantomData<(Err, State, Ctx, In)>,
}

impl<In: ?Sized, Err, State, Ctx> Copy for Any<In, Err, State, Ctx> {}
impl<In: ?Sized, Err, State, Ctx> Clone for Any<In, Err, State, Ctx> {
    fn clone(&self) -> Self {
        Self {
            phantom: PhantomData,
        }
    }
}

impl<'a, In, Err, State, Ctx> Parser<'a, In, In::Token, Err, State, Ctx> for Any<In, Err, State, Ctx>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, In::Token, Err> {
        let before = inp.save();
        match inp.next() {
            (_, Some(tok)) => Ok(M::bind(|| tok)),
            (at, found) => Err(Located::at(
                at,
                Err::expected_found(None, found, inp.span_since(before)),
            )),
        }
    }

    go_extra!(In::Token);
}

/// A parser that accepts any input (but not the end of input).
///
/// The output type of this parser is `I`, the input that was found.
///
/// # Examples
///
/// ```
/// # use chumsky::zero_copy::{prelude::*, error::Simple};
/// let any = any();
///
/// assert_eq!(any.parse("a").into_result(), Ok('a'));
/// assert_eq!(any.parse("7").into_result(), Ok('7'));
/// assert_eq!(any.parse("\t").into_result(), Ok('\t'));
/// assert!(any.parse("").has_errors());
/// ```
pub const fn any<In: Input + ?Sized, Err: Error<In>, State, Ctx>() -> Any<In, Err, State, Ctx> {
    Any {
        phantom: PhantomData,
    }
}

/// See [`take_until`].
pub struct TakeUntil<P, In: ?Sized, OP, C = (), Err = EmptyErr, State = (), Ctx = ()> {
    until: P,
    // FIXME try remove OP? See comment in Map declaration
    phantom: PhantomData<(OP, C, Err, State, Ctx, In)>,
}

impl<'a, In, Err, State, Ctx, P, OP, C> TakeUntil<P, In, OP, C, Err, State, Ctx>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
    P: Parser<'a, In, OP, Err, State, Ctx>,
{
    /// Set the type of [`Container`] to collect into.
    pub fn collect<D: Container<OP>>(self) -> TakeUntil<P, In, OP, D, Err, State> {
        TakeUntil {
            until: self.until,
            phantom: PhantomData,
        }
    }
}

impl<P: Copy, In: ?Sized, C, Err, State> Copy for TakeUntil<P, In, C, Err, State> {}
impl<P: Clone, In: ?Sized, C, Err, State> Clone for TakeUntil<P, In, C, Err, State> {
    fn clone(&self) -> Self {
        TakeUntil {
            until: self.until.clone(),
            phantom: PhantomData,
        }
    }
}

/// A parser that accepts any number of inputs until a terminating pattern is reached.
///
/// The output type of this parser is `(Vec<I>, O)`, a combination of the preceding inputs and the output of the
/// final patterns.
///
/// # Examples
///
/// ```
/// # use chumsky::zero_copy::{prelude::*, error::Simple};
/// let single_line = just("//")
///     .then(take_until(text::newline()))
///     .ignored();
///
/// let multi_line = just("/*")
///     .then(take_until(just("*/")))
///     .ignored();
///
/// let comment = single_line.or(multi_line);
///
/// let tokens = text::ident()
///     .padded()
///     .padded_by(comment
///         .padded()
///         .repeated()
///         .collect::<Vec<_>>())
///     .repeated()
///     .collect::<Vec<_>>();
///
/// assert_eq!(tokens.parse(r#"
///     // These tokens...
///     these are
///     /*
///         ...have some
///         multi-line...
///     */
///     // ...and single-line...
///     tokens
///     // ...comments between them
/// "#).into_result(), Ok(vec!["these", "are", "tokens"]));
/// ```
pub const fn take_until<'a, P, OP, In, Err, State>(until: P) -> TakeUntil<P, In, OP, (), Err, State>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
    P: Parser<'a, In, OP, Err, State>,
{
    TakeUntil {
        until,
        phantom: PhantomData,
    }
}

impl<'a, P, OP, In, Err, State, Ctx, C> Parser<'a, In, (C, OP), Err, State, Ctx> for TakeUntil<P, In, OP, C, Err, State>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
    P: Parser<'a, In, OP, Err, State, Ctx>,
    C: Container<In::Token>,
{
    type Config = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, (C, OP), Err> {
        let mut output = M::bind(|| C::default());

        loop {
            let start = inp.save();
            let e = match self.until.go::<M>(inp) {
                Ok(out) => break Ok(M::combine(output, out, |output, out| (output, out))),
                Err(e) => e,
            };

            inp.rewind(start);

            match inp.next() {
                (_, Some(tok)) => {
                    output = M::map(output, |mut output: C| {
                        output.push(tok);
                        output
                    })
                }
                (_, None) => break Err(e),
            }
        }
    }

    go_extra!((C, OP));
}

/// See [`fn@todo`].
pub struct Todo<In: ?Sized, Out, Err>(PhantomData<(Out, Err, In)>);

impl<In: ?Sized, Out, Err> Copy for Todo<In, Out, Err> {}
impl<In: ?Sized, Out, Err> Clone for Todo<In, Out, Err> {
    fn clone(&self) -> Self {
        *self
    }
}

/// A parser that can be used wherever you need to implement a parser later.
///
/// This parser is analagous to the [`todo!`] and [`unimplemented!`] macros, but will produce a panic when used to
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
/// # use chumsky::zero_copy::prelude::*;
/// let int = just("0x").ignore_then(todo())
///     .or(just("0b").ignore_then(text::digits(2)))
///     .or(text::int(10));
///
/// // Decimal numbers are parsed
/// assert_eq!(int.parse("12").into_result(), Ok("12"));
/// // Binary numbers are parsed
/// assert_eq!(int.parse("0b00101").into_result(), Ok("00101"));
/// // Parsing hexidecimal numbers results in a panic because the parser is unimplemented
/// int.parse("0xd4");
/// ```
pub const fn todo<In: Input + ?Sized, Out, Err: Error<In>>() -> Todo<In, Out, Err> {
    Todo(PhantomData)
}

impl<'a, In, Out, Err, State, Ctx> Parser<'a, In, Out, Err, State, Ctx> for Todo<In, Out, Err>
where
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
{
    type Config = ();

    fn go<M: Mode>(&self, _inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, Out, Err> {
        todo!("Attempted to use an unimplemented parser")
    }

    go_extra!(Out);
}

/// See [`choice`].
pub struct Choice<T, O> {
    parsers: T,
    phantom: PhantomData<O>,
}

impl<T: Copy, O> Copy for Choice<T, O> {}
impl<T: Clone, O> Clone for Choice<T, O> {
    fn clone(&self) -> Self {
        Self {
            parsers: self.parsers.clone(),
            phantom: PhantomData,
        }
    }
}

/// Parse using a tuple of many parsers, producing the output of the first to successfully parse.
///
/// This primitive has a twofold improvement over a chain of [`Parser::or`] calls:
///
/// - Rust's trait solver seems to resolve the [`Parser`] impl for this type much faster, significantly reducing
///   compilation times.
///
/// - Parsing is likely a little faster in some cases because the resulting parser is 'less careful' about error
///   routing, and doesn't perform the same fine-grained error prioritisation that [`Parser::or`] does.
///
/// These qualities make this parser ideal for lexers.
///
/// The output type of this parser is the output type of the inner parsers.
///
/// # Examples
/// ```
/// # use chumsky::zero_copy::prelude::*;
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
///     text::keyword::<_, _, _, Simple<str>, ()>("if").to(Token::If),
///     text::keyword("for").to(Token::For),
///     text::keyword("while").to(Token::While),
///     text::keyword("fn").to(Token::Fn),
///     text::int(10).from_str().unwrapped().map(Token::Int),
///     text::ident().map(Token::Ident),
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
pub const fn choice<T, O>(parsers: T) -> Choice<T, O> {
    Choice {
        parsers,
        phantom: PhantomData,
    }
}

macro_rules! impl_choice_for_tuple {
    () => {};
    ($head:ident $($X:ident)*) => {
        impl_choice_for_tuple!($($X)*);
        impl_choice_for_tuple!(~ $head $($X)*);
    };
    (~ $($X:ident)*) => {
        #[allow(unused_variables, non_snake_case)]
        impl<'a, In, Err, State, Ctx, $($X),*, Out> Parser<'a, In, Out, Err, State, Ctx> for Choice<($($X,)*), Out>
        where
            In: Input + ?Sized,
            Err: Error<In>,
            State: 'a,
            $($X: Parser<'a, In, Out, Err, State, Ctx>),*
        {
            type Config = ();

            fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, Out, Err> {
                let before = inp.save();

                let Choice { parsers: ($($X,)*), .. } = self;

                let mut err: Option<Located<Err>> = None;
                $(
                    match $X.go::<M>(inp) {
                        Ok(out) => return Ok(out),
                        Err(e) => {
                            // TODO: prioritise errors
                            err = Some(match err {
                                Some(err) => err.prioritize(e, |a, b| a.merge(b)),
                                None => e,
                            });
                            inp.rewind(before);
                        },
                    };
                )*

                Err(err.unwrap_or_else(|| Located::at(inp.last_pos(), Err::expected_found(None, None, inp.span_since(before)))))
            }

            go_extra!(Out);
        }
    };
}

impl_choice_for_tuple!(A_ B_ C_ D_ E_ F_ G_ H_ I_ J_ K_ L_ M_ N_ O_ P_ Q_ S_ T_ U_ V_ W_ X_ Y_ Z_);

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
        impl<'a, In, Err, State, Ctx, $($X),*, $($O),*> Parser<'a, In, ($($O,)*), Err, State, Ctx> for Group<($($X,)*)>
        where
            In: Input + ?Sized,
            Err: Error<In>,
            State: 'a,
            $($X: Parser<'a, In, $O, Err, State, Ctx>),*
        {
            type Config = ();

            fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, ($($O,)*), Err> {
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
