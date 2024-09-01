use std::error::Error;

const URL_START: &str = "https://github.com/zesterer/chumsky/blob/";

fn main() -> Result<(), Box<dyn Error>> {
    #[cfg(feature = "docsrs")]
    {
        use vergen_gix::{Emitter, GixBuilder};

        let gitcl = GixBuilder::all_git()?;
        Emitter::default()
            .add_instructions(&gitcl)?
            .emit_and_set()?;
        println!(
            "cargo:rustc-env=CHUMSKY_REPO_URL={URL_START}{}",
            std::env::var("VERGEN_GIT_SHA").unwrap()
        );
    }
    #[cfg(not(feature = "docsrs"))]
    {
        println!(
            "cargo:rustc-env=CHUMSKY_REPO_URL={URL_START}{}",
            std::env::var("CARGO_PKG_VERSION").unwrap()
        );
    }
    Ok(())
}
