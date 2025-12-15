//! Unstable utilities for debugging in-development parsers.
//!
//! See [`Parser::debug`].

use super::*;

#[doc(hidden)]
#[derive(Debug)]
pub enum SeqInfo {
    Char(char),
    String(String),
    Opaque(String),
    Unknown(String),
}

impl SeqInfo {
    fn show(&self) -> String {
        match self {
            Self::Char(c) => format!("'{c}'"),
            Self::String(s) => format!("\"{s}\""),
            Self::Opaque(s) => s.to_string(),
            Self::Unknown(s) => s.to_string(),
        }
    }
}

#[doc(hidden)]
#[derive(Debug)]
pub enum NodeInfo {
    Unknown(String),
    // The root of a recursive definition
    Recursive(usize, Box<Self>),
    RecursiveRef(usize),
    Repeated(core::ops::Range<u64>, Box<Self>),
    SeparatedBy(Box<Self>, Box<Self>),
    Choice(Vec<Self>),
    Any,
    Just(SeqInfo),
    OneOf(SeqInfo),
    NoneOf(SeqInfo),
    Then(Box<Self>, Box<Self>),
    Padded(Box<Self>),
    Filter(Box<Self>),
    OrNot(Box<Self>),
    Labelled(String, Box<Self>),
    Builtin(String),
    NestedIn(Box<Self>, Box<Self>),
}

impl NodeInfo {
    // ctx { 0 = any, 1 = or, 2 = then }
    fn bnf_inner(&self, depth: usize, defs: &mut Vec<String>, ctx: usize) -> String {
        match self {
            Self::Unknown(s) => format!("<unknown: {s}>"),
            Self::Recursive(r, inner) => {
                let def = inner.bnf_inner(1, defs, 0);
                defs.push(format!("def_{r} ::= {def};"));
                format!("def_{r}")
            }
            Self::Repeated(_, inner) => format!("{{ {} }}", inner.bnf_inner(depth, defs, 0)),
            Self::SeparatedBy(inner, sep) => format!(
                "{{ {} [{}]}}",
                inner.bnf_inner(depth, defs, 2),
                sep.bnf_inner(depth, defs, 0)
            ),
            Self::OrNot(inner) => format!("[ {} ]", inner.bnf_inner(depth, defs, 0)),
            Self::Choice(inners) => {
                let s = inners
                    .iter()
                    .map(|i| i.bnf_inner(depth + 1, defs, 1))
                    .collect::<Vec<_>>()
                    .join(&format!("\n{}| ", "  ".repeat(depth)));
                if ctx == 1 || ctx == 0 {
                    s
                } else {
                    format!("({s})")
                }
            }
            Self::Just(seq) => seq.show(),
            Self::OneOf(seq) => format!("one_of({})", seq.show()),
            Self::NoneOf(seq) => format!("none_of({})", seq.show()),
            Self::Then(a, b) => {
                let s = format!(
                    "{} {}",
                    a.bnf_inner(depth, defs, 2),
                    b.bnf_inner(depth, defs, 2)
                );
                if ctx == 1 || ctx == 0 {
                    s
                } else {
                    format!("({s})")
                }
            }
            Self::Any => "any".to_string(),
            Self::Builtin(s) => s.to_string(),
            Self::NestedIn(a, b) => format!(
                "({}).nested_in({})",
                a.bnf_inner(depth, defs, 0),
                b.bnf_inner(depth, defs, 0)
            ),
            Self::Padded(inner) | Self::Filter(inner) | Self::Labelled(_, inner) => {
                inner.bnf_inner(depth, defs, ctx)
            }
            Self::RecursiveRef(r) => format!("def_{r}"),
        }
    }

    fn railroad_inner(&self, defs: &mut Vec<Box<dyn railroad::Node>>) -> Box<dyn railroad::Node> {
        use railroad::*;
        match self {
            Self::Unknown(s) => Box::new(Comment::new(s.to_string())),
            Self::Recursive(r, inner) => {
                let inner = inner.railroad_inner(defs);
                defs.push(Box::new(LabeledBox::new(
                    Sequence::new(vec![
                        Box::new(SimpleStart) as Box<dyn Node>,
                        inner,
                        Box::new(SimpleEnd),
                    ]),
                    Terminal::new(format!("def_{r}")),
                )));
                Box::new(Terminal::new(format!("def_{r}")))
            }
            Self::Repeated(_, inner) => Box::new(Repeat::new(inner.railroad_inner(defs), Empty)),
            Self::SeparatedBy(inner, sep) => Box::new(Repeat::new(
                inner.railroad_inner(defs),
                sep.railroad_inner(defs),
            )),
            Self::Choice(inners) => Box::new(Choice::new(
                inners.iter().map(|i| i.railroad_inner(defs)).collect(),
            )),
            Self::Just(seq) => Box::new(NonTerminal::new(seq.show())),
            Self::OneOf(seq) => Box::new(Terminal::new(format!("one_of({})", seq.show()))),
            Self::NoneOf(seq) => Box::new(Terminal::new(format!("none_of({})", seq.show()))),
            Self::Then(a, b) => Box::new(Sequence::new(vec![
                a.railroad_inner(defs),
                b.railroad_inner(defs),
            ])),
            Self::RecursiveRef(r) => Box::new(Terminal::new(format!("def_{r}"))),
            // Self::Padded(inner) => Box::new(Sequence::new(vec![
            //     Box::new(Terminal::new(format!("whitespace"))) as Box<dyn Node>,
            //     inner.railroad_inner(defs),
            //     Box::new(Terminal::new(format!("whitespace"))),
            // ])),
            Self::Padded(inner) => inner.railroad_inner(defs),
            Self::Filter(inner) => Box::new(LabeledBox::new(
                inner.railroad_inner(defs),
                Comment::new("filtered".to_string()),
            )),
            Self::Labelled(label, inner) => Box::new(LabeledBox::new(
                inner.railroad_inner(defs),
                NonTerminal::new(label.to_string()),
            )),
            Self::Builtin(s) => Box::new(Terminal::new(s.to_string())),
            Self::NestedIn(inner, outer) => Box::new(LabeledBox::new(
                Box::new(LabeledBox::new(
                    outer.railroad_inner(defs),
                    NonTerminal::new("outer".to_string()),
                )),
                Box::new(LabeledBox::new(
                    Sequence::new(vec![
                        Box::new(SimpleStart) as Box<dyn Node>,
                        inner.railroad_inner(defs),
                        Box::new(SimpleEnd),
                    ]),
                    NonTerminal::new("inner".to_string()),
                )),
            )),
            Self::Any => Box::new(Terminal::new("any".to_string())),
            Self::OrNot(inner) => Box::new(Optional::new(inner.railroad_inner(defs))),
        }
    }
}

#[doc(hidden)]
#[derive(Default)]
pub struct NodeScope {
    rec_count: usize,
    // (ptr, index, name)
    rec: Vec<(usize, usize)>,
}

impl NodeScope {
    pub fn lookup_rec(&mut self, ptr: usize, f: impl FnOnce(&mut Self) -> NodeInfo) -> NodeInfo {
        self.rec
            .iter()
            .rev()
            .find(|(p, _)| *p == ptr)
            .map(|(_, r)| NodeInfo::RecursiveRef(*r))
            .unwrap_or_else(|| {
                self.rec_count += 1;
                self.rec.push((ptr, self.rec_count));
                NodeInfo::Recursive(self.rec_count, Box::new(f(self)))
            })
    }
}

/// A catch-all box of tricks for debugging a parser.
pub struct DebugInfo<'a> {
    pub(crate) node_info: NodeInfo,
    pub(crate) phantom: PhantomData<&'a ()>,
}

impl<'a> DebugInfo<'a> {
    /// Generate a string containing an [eBNF](https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form#EBNF) grammar for this parser.
    ///
    /// The exact format of the grammar definition is not specified, and is only intended to be read by a human being.
    pub fn to_ebnf(&self) -> String {
        let mut defs = Vec::new();
        let def = self.node_info.bnf_inner(1, &mut defs, 0);
        defs.push(def);
        defs.join("\n\n")
    }

    /// Generate a human-readable [railroad diagram](https://en.wikipedia.org/wiki/Syntax_diagram) that describes the grammar.
    ///
    /// The resulting diagram is in [SVG](https://en.wikipedia.org/wiki/SVG) format and may be printed to the console, written to a file, etc.
    ///
    /// The exact format of the diagram is not specified and its quality may depend heavily on annotations, such as [`Parser::labelled`].
    /// Aspects of the grammar may also not be captured. For example, context-sensitive parsers are largely ignored today.
    ///
    /// # Examples
    ///
    /// Here is a generated railroad diagram for the example JSON parser. See `examples/json.rs` in the repository.
    ///
    /// ![A railroad diagram of the grammar for JSON](https://github.com/zesterer/chumsky/raw/main/misc/json-railroad.svg)
    pub fn to_railroad_svg(&self) -> impl core::fmt::Display + Clone {
        use railroad::*;

        let mut seq = Sequence::default();
        let mut defs = Vec::new();
        let def = self.node_info.railroad_inner(&mut defs);
        defs.push(def);
        seq.push(Rc::new(VerticalGrid::new(defs)) as Rc<dyn Node>);

        let mut dia = Diagram::new(seq);

        dia.add_element(
            svg::Element::new("style")
                .set("type", "text/css")
                .text(DEFAULT_CSS),
        );
        dia
    }
}
