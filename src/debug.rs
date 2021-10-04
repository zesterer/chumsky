use super::*;

use std::{
    borrow::Cow,
    panic::Location,
};

/// Information about a specific parser.
pub struct ParserInfo {
    name: Cow<'static, str>,
    location: Location<'static>,
}

/// An event that occurred during parsing.
pub enum ParseEvent {}

pub struct ParseScope {
    events: Vec<ParseEvent>,
}

impl ParseScope {

}

trait Scope {
    fn emit_with<F: FnOnce() -> ParseEvent>(&mut self, f: F);
}

pub trait Debugger {
    fn scope<R, F: FnOnce(&mut Self) -> R>(&mut self, f: F) -> R;
    fn emit_with<F: FnOnce() -> ParseEvent>(&mut self, f: F);
}

// Verbose

pub struct Verbose {
    events: Vec<Result<ParseEvent, Self>>,
}

impl Debugger for Verbose {
    fn scope<R, F: FnOnce(&mut Self) -> R>(&mut self, f: F) -> R {
        let mut verbose = Verbose {
            events: Vec::new(),
        };
        let res = f(&mut verbose);
        self.events.push(Err(verbose));
        res
    }

    fn emit_with<F: FnOnce() -> ParseEvent>(&mut self, f: F) {
        self.events.push(Ok(f()));
    }
}

// Silent

pub struct Silent;

impl Debugger for Silent {
    fn scope<R, F: FnOnce(&mut Self) -> R>(&mut self, f: F) -> R { f(self) }
    fn emit_with<F: FnOnce() -> ParseEvent>(&mut self, f: F) {}
}
