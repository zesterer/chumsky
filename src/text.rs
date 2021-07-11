use super::*;

/// The type of a parser that accepts (and ignores) any number of characters.
pub type Padding<E> = Repeated<Ignored<Filter<fn(&char) -> bool, E>, char>>;

/// The type of a parser that accepts (and ignores) any number of characters after another pattern.
pub type Padded<P, O> = Map<Then<P, Padding<<P as Parser<char, O>>::Error>>, fn((O, Vec<()>)) -> O, (O, Vec<()>)>;

/// A trait containing text-specific functionality that extends the [`Parser`] trait.
pub trait TextParser<O>: Parser<char, O> {
    /// Parse a pattern, and then ignore any number of whitespace characters that appear after it.
    fn padded(self) -> Padded<Self, O> where Self: Sized {
        Map(Then(self, whitespace::<Self::Error>()), |(o, _)| o, PhantomData)
    }
}

impl<O, P: Parser<char, O>> TextParser<O> for P {}

/// A parser that accepts (and ignores) any number of whitespace characters.
pub fn whitespace<E: Error<char>>() -> Padding<E> {
    filter((|c: &char| c.is_whitespace()) as _).ignored().repeated()
}
