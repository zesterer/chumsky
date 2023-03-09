// To generate docs, use `RUSTDOCFLAGS="--cfg docsrs" cargo +nightly doc --all-features`

#![doc = include_str!("../tutorial/intro.md")]
use super::*;

pub mod getting_started {
    #![doc = include_str!("../tutorial/getting_started.md")]
    use super::*;
}

pub mod key_concepts {
    #![doc = include_str!("../tutorial/key_concepts.md")]
    use super::*;
}
