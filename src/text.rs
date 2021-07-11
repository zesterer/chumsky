use super::*;

type Whitespace<E> = Repeated<Ignored<Matches<fn(&char) -> bool, E>, char>>;

/// A parser, right-padded by whitespace
type Padded<P, O> = Map<Then<P, Whitespace<<P as Parser<char, O>>::Error>>, fn((O, Vec<char>)) -> O, (O, Vec<char>)>;

pub trait TextParser<O, E: Error<char>>: Parser<char, O, Error = E> {
    fn padded(self) -> Padded<Self, O> where Self: Sized {
        Map(Then(self, whitespace::<E>()), |(o, _)| o, PhantomData)
    }
}

pub fn whitespace<E: Error<char>>() -> Whitespace<E> {
    matches((|c: &char| c.is_whitespace()) as _).ignored().repeated()
}
