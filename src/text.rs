use super::*;

type Whitespace = Repeated<Ignored<Matches<fn(&char) -> bool>, char>>;

/// A parser, right-padded by whitespace
type Padded<P, O> = Map<Then<P, Whitespace>, fn((O, Vec<char>)) -> O, (O, Vec<char>)>;

pub trait TextParser<O>: Parser<char, O> {
    fn padded(self) -> Padded<Self, O> where Self: Sized {
        Map(Then(self, whitespace()), |(o, _)| o, PhantomData)
    }
}

pub fn whitespace() -> Whitespace {
    matches((|c: &char| c.is_whitespace()) as _).ignored().repeated()
}
