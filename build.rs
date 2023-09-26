use std::error::Error;
#[cfg(feature = "docsrs")]
use vergen::EmitBuilder;

fn main() -> Result<(), Box<dyn Error>> {
    emit_git_metadata()?;
    Ok(())
}

#[cfg(feature = "docsrs")]
fn emit_git_metadata() -> Result<(), Box<dyn Error>> {
    // Emit the instructions
    EmitBuilder::builder().all_git().emit()?;
    Ok(())
}

#[cfg(not(feature = "docsrs"))]
fn emit_git_metadata() -> Result<(), Box<dyn Error>> {
    Ok(())
}
