use super::*;

/// The type of a parser that accepts (and ignores) any number of characters.
pub type Padding<I, E> = Custom<fn(&mut StreamOf<I, E>) -> PResult<(), E>, E>;

/// The type of a parser that accepts (and ignores) any number of characters before or after another pattern.
pub type Padded<P, I, O> = PaddedBy<PaddingFor<Padding<I, <P as Parser<I, O>>::Error>, P, (), O>, Padding<I, <P as Parser<I, O>>::Error>, O, ()>;

/// A trait implemented by textual character types (currently, [`u8`] and [`char`]).
pub trait Character: Copy + PartialEq {
    fn is_whitespace(&self) -> bool;
    fn digit_zero() -> Self;
    fn is_digit(&self, radix: u32) -> bool;
}

impl Character for u8 {
    fn is_whitespace(&self) -> bool { self.is_ascii_whitespace() }
    fn digit_zero() -> Self { b'0' }
    fn is_digit(&self, radix: u32) -> bool { (*self as char).is_digit(radix) }
}

impl Character for char {
    fn is_whitespace(&self) -> bool { char::is_whitespace(*self) }
    fn digit_zero() -> Self { '0' }
    fn is_digit(&self, radix: u32) -> bool { char::is_digit(*self, radix) }
}

/// A trait containing text-specific functionality that extends the [`Parser`] trait.
pub trait TextParser<I: Character, O>: Parser<I, O> {
    /// Parse a pattern, allowing whitespace both before and after.
    fn padded(self) -> Padded<Self, I, O> where Self: Sized {
        whitespace().ignore_then(self).then_ignore(whitespace())
    }
}

impl<I: Character, O, P: Parser<I, O>> TextParser<I, O> for P {}

/// A parser that accepts (and ignores) any number of whitespace characters.
pub fn whitespace<C: Character, E: Error<Token = C>>() -> Padding<C, E> {
    custom(|stream: &mut StreamOf<C, E>| {
        loop {
            let state = stream.save();
            if stream.next().2.map_or(true, |b| !b.is_whitespace()) {
                stream.revert(state);
                break (Vec::new(), Ok(((), None)));
            }
        }
    })
}

/// A parser that accepts (and ignores) any newline characters or character sequences.
pub fn newline<E: Error<Token = char>>() -> impl Parser<char, (), Error = E> {
    just('\r').or_not().ignore_then(just('\n'))
        .or(just('\x0B')) // Vertical tab
        .or(just('\x0C')) // Form feed
        .or(just('\x0D')) // Carriage return
        .or(just('\u{0085}')) // Next line
        .or(just('\u{2028}')) // Line separator
        .or(just('\u{2029}')) // Paragraph separator
        .ignored()
}

/// A parser that accepts one or more ASCII digits.
pub fn digits<C: Character, E: Error<Token = C>>(radix: u32) -> Repeated<Filter<impl Fn(&C) -> bool + Clone + Send + Sync + 'static, E>> {
    filter(move |c: &C| c.is_digit(radix)).repeated_at_least(1)
}

/// A parser that accepts a positive integer.
///
/// An integer is defined as a non-empty sequence of ASCII digits, where the first digit is non-zero or the sequence
/// has length one.
pub fn int<C: Character, E: Error<Token = C>>(radix: u32) -> impl Parser<C, Vec<C>, Error = E> + Copy + Clone {
    filter(move |c: &C| c.is_digit(radix) && c != &C::digit_zero()).map(Some)
        .chain(filter(move |c: &C| c.is_digit(radix)).repeated())
        .or(just(C::digit_zero()).map(|c| vec![c]))
}

/// A parser that accepts a C-style identifier.
///
/// An identifier is defined as an ASCII alphabetic character or an underscore followed by any number of alphanumeric
/// characters or underscores. The regex pattern for it is `[a-zA-Z_][a-zA-Z0-9_]*`.
pub fn ident<E: Error<Token = char>>() -> impl Parser<char, Vec<char>, Error = E> + Copy + Clone {
    filter(|c: &char| c.is_ascii_alphabetic() || *c == '_').map(Some)
        .chain(filter(|c: &char| c.is_ascii_alphanumeric() || *c == '_').repeated())
}
