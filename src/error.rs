use std::fmt;

pub trait Error<I>: Sized {
    fn position(&self) -> usize;
    fn expected_found(position: usize, expected: Option<I>, found: Option<I>) -> Self;
    fn merge(self, other: Self) -> Self {
        if self.position() < other.position() {
            self
        } else {
            other
        }
    }
}

#[derive(Debug)]
pub struct BasicError<I> {
    position: usize,
    expected: Vec<I>,
    found: Option<I>,
}

impl<I> Error<I> for BasicError<I> {
    fn position(&self) -> usize { self.position }
    fn expected_found(position: usize, expected: Option<I>, found: Option<I>) -> Self {
        Self {
            position,
            expected: expected.into_iter().collect(),
            found,
        }
    }
    fn merge(mut self, mut other: Self) -> Self {
        if self.position() < other.position() {
            self
        } else if self.position() > other.position() {
            other
        } else {
            self.expected.append(&mut other.expected);
            self
        }
    }
}

impl<I: fmt::Display> fmt::Display for BasicError<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(found) = &self.found {
            write!(f, "found '{}' ", found)?;
        } else {
            write!(f, "the input ended ")?;
        }

        write!(f, "at {}", self.position)?;

        match self.expected.as_slice() {
            [] => {},
            [expected] => write!(f, " but '{}' was expected", expected)?,
            [_, ..] => write!(f, " but one of '{}' expected", self.expected
                .iter()
                .map(|expected| expected.to_string())
                .collect::<Vec<_>>()
                .join(", "))?,
        }

        Ok(())
    }
}
impl<I: fmt::Debug + fmt::Display> std::error::Error for BasicError<I> {}
