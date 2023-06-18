//! Text parsers for [chumsky].

pub mod char;
pub mod ext;
pub mod input;
#[cfg(feature = "regex")]
pub mod regex;
pub mod text;

pub mod prelude {
    pub use crate::{char::Char, ext::ParserExt, text};

    #[cfg(feature = "regex")]
    pub use crate::regex::regex;
}
