use super::*;

/// The type of a parser that accepts (and ignores) any number of characters.
pub type Padding<E> = Repeated<Ignored<Filter<fn(&char) -> bool, E>, char>>;

/// The type of a parser that accepts (and ignores) any number of characters before or after another pattern.
pub type Padded<P, O> = PaddedBy<PaddingFor<Padding<<P as Parser<char, O>>::Error>, P, Vec<()>, O>, Padding<<P as Parser<char, O>>::Error>, O, Vec<()>>;

/// A trait containing text-specific functionality that extends the [`Parser`] trait.
pub trait TextParser<O>: Parser<char, O> {
    /// Parse a pattern, allowing whitespace both before and after.
    fn padded(self) -> Padded<Self, O> where Self: Sized {
        whitespace().padding_for(self).padded_by(whitespace())
    }
}

impl<O, P: Parser<char, O>> TextParser<O> for P {}

/// A parser that accepts (and ignores) any number of whitespace characters.
pub fn whitespace<E: Error<Token = char>>() -> Padding<E> {
    filter((|c: &char| c.is_whitespace()) as _).ignored().repeated()
}

/// A parser that accepts (and ignores) any newline characters or character sequences.
pub fn newline<E: Error<Token = char>>() -> impl Parser<char, (), Error = E> {
    just('\r').or_not().padding_for(just('\n'))
        .or(just('\x0B')) // Vertical tab
        .or(just('\x0C')) // Form feed
        .or(just('\x0D')) // Carriage return
        .or(just('\u{0085}')) // Next line
        .or(just('\u{2028}')) // Line separator
        .or(just('\u{2029}')) // Paragraph separator
        .ignored()
}

/// A parser that accepts one or more ASCII digits.
pub fn digits<E: Error<Token = char>>() -> Repeated<Filter<fn(&char) -> bool, E>> {
    filter(char::is_ascii_digit as _).repeated_at_least(1)
}

/// A parser that accepts a positive integer.
///
/// An integer is defined as a non-empty sequence of ASCII digits, where the first digit is non-zero or the sequence
/// has length one.
pub fn int<E: Error<Token = char>>() -> impl Parser<char, Vec<char>, Error = E> + Copy + Clone {
    filter(|c: &char| c.is_ascii_digit() && *c != '0').map(Some)
        .chain(filter(char::is_ascii_digit).repeated())
        .or(just('0').map(|c| vec![c]))
}

/// A parser that accepts a C-style identifier.
///
/// An identifier is defined as an ASCII alphabetic character or an underscore followed by any number of alphanumeric
/// characters or underscores. The regex pattern for it is `[a-zA-Z_][a-zA-Z0-9_]*`.
pub fn ident<E: Error<Token = char>>() -> impl Parser<char, Vec<char>, Error = E> + Copy + Clone {
    filter(|c: &char| c.is_ascii_alphabetic() || *c == '_').map(Some)
        .chain(filter(|c: &char| c.is_ascii_alphanumeric() || *c == '_').repeated())
}
