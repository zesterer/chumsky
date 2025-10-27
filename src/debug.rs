#![doc(hidden)]

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
            Self::Opaque(s) => format!("{s}"),
            Self::Unknown(s) => format!("{s}"),
        }
    }
}

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
            Self::Any => format!("any"),
            Self::Padded(inner) | Self::Filter(inner) | Self::Labelled(_, inner) => {
                inner.bnf_inner(depth, defs, ctx)
            }
            Self::RecursiveRef(r) => format!("def_{r}"),
            _ => todo!("{:?}", self),
        }
    }

    pub fn to_ebnf(&self) -> String {
        let mut defs = Vec::new();
        let def = self.bnf_inner(1, &mut defs, 0);
        defs.push(def);
        defs.join("\n\n")
    }

    fn railroad_inner(&self, defs: &mut Vec<Box<dyn railroad::Node>>) -> Box<dyn railroad::Node> {
        use railroad::*;
        match self {
            Self::Unknown(s) => Box::new(Comment::new(format!("{s}"))),
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
            Self::Padded(inner) => Box::new(Sequence::new(vec![
                Box::new(Terminal::new(format!("whitespace"))) as Box<dyn Node>,
                inner.railroad_inner(defs),
                Box::new(Terminal::new(format!("whitespace"))),
            ])),
            // Self::Padded(inner) => Box::new(LabeledBox::new(
            //     inner.railroad_inner(defs),
            //     Comment::new(format!("padded")),
            // )),
            Self::Filter(inner) => Box::new(LabeledBox::new(
                inner.railroad_inner(defs),
                Comment::new(format!("filtered")),
            )),
            Self::Labelled(label, inner) => Box::new(LabeledBox::new(
                inner.railroad_inner(defs),
                NonTerminal::new(format!("{label}")),
            )),
            Self::Any => Box::new(Terminal::new(format!("any"))),
            Self::OrNot(inner) => Box::new(Optional::new(inner.railroad_inner(defs))),
            _ => todo!("{:?}", self),
        }
    }

    pub fn to_railroad_svg(&self) -> impl core::fmt::Display {
        use railroad::*;

        let mut seq = Sequence::default();
        let mut defs = Vec::new();
        let def = self.railroad_inner(&mut defs);
        defs.push(def);
        seq.push(Box::new(VerticalGrid::new(defs)) as Box<dyn Node>);

        let mut dia = Diagram::new(seq);

        dia.add_element(
            svg::Element::new("style")
                .set("type", "text/css")
                .text(DEFAULT_CSS),
        );
        dia
    }
}

#[derive(Default)]
pub struct NodeScope {
    rec_count: usize,
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
