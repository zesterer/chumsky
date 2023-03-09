// To generate docs with the guide, use `RUSTDOCFLAGS="--cfg docsrs" cargo +nightly doc --all-features`

#![doc = include_str!("../guide/intro.md")]
use super::*;

pub mod getting_started {
    #![doc = include_str!("../guide/getting_started.md")]
    use super::*;
}

pub mod key_concepts {
    #![doc = include_str!("../guide/key_concepts.md")]
    use super::*;
}
