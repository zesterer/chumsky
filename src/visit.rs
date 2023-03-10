use std::convert::TryFrom;
use super::*;
use crate::primitive::*;
use crate::combinator::*;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct SizeHint {
    lower: usize,
    upper: Option<usize>,
}

impl SizeHint {
    fn new(lower: usize, upper: Option<usize>) -> SizeHint {
        SizeHint {
            lower,
            upper,
        }
    }

    fn and(lhs: SizeHint, rhs: SizeHint) -> SizeHint {
        let lower = lhs.lower + rhs.lower;
        let upper = lhs.upper.zip(rhs.upper).map(|(l, r)| l + r);
        SizeHint::new(lower, upper)
    }

    fn or(lhs: SizeHint, rhs: SizeHint) -> SizeHint {
        let lower = usize::min(lhs.lower, rhs.lower);
        let upper = lhs.upper.zip(rhs.upper).map(|(l, r)| usize::max(l, r));
        SizeHint::new(lower, upper)
    }

    fn repeat(lhs: SizeHint, rhs: SizeHint) -> SizeHint {
        let lower = lhs.lower * rhs.lower;
        let upper = lhs.upper.zip(rhs.upper).map(|(this, reps)| {
            reps * this
        });
        SizeHint::new(lower, upper)
    }

    pub fn lower(&self) -> usize {
        self.lower
    }

    pub fn upper(&self) -> Option<usize> {
        self.upper
    }
}

pub struct ParserInfo<'a, P: ?Sized> {
    pub(crate) name: &'a str,
    pub(crate) size_hint: SizeHint,
    pub(crate) parser: &'a P,
}

impl<'a, P> ParserInfo<'a, P>
where
    P: ?Sized + Visitable,
{
    fn new(parser: &'a P, name: &'a str, size_hint: SizeHint) -> ParserInfo<'a, P> {
        ParserInfo {
            name,
            size_hint,
            parser,
        }
    }

    pub fn visit<V: ParserVisitor>(&self, visitor: &mut V) {
        self.parser.visit_children(visitor);
    }
}

pub trait ParserVisitor {
    fn visit<P>(&mut self, info: &ParserInfo<'_, P>)
    where
        P: ?Sized + Visitable;
}

pub trait Visitable {
    fn info(&self) -> ParserInfo<'_, Self>;

    fn visit<V: ParserVisitor>(&self, visitor: &mut V) {
        let info = self.info();
        visitor.visit(&info);
    }

    fn visit_children<V: ParserVisitor>(&self, visitor: &mut V) {
        #![allow(unused_variables)]
    }
}

impl<A, O, C> Visitable for Collect<A, O, C>
where
    A: Visitable,
{
    fn info(&self) -> ParserInfo<'_, Self> {
        ParserInfo::new(
            self,
            "collect",
            self.parser.info().size_hint
        )
    }

    fn visit_children<V: ParserVisitor>(&self, visitor: &mut V) {
        self.parser.visit(visitor);
    }
}

impl<A, OA> Visitable for Ignored<A, OA>
where
    A: Visitable
{
    fn info(&self) -> ParserInfo<'_, Self> {
        ParserInfo::new(
            self,
            "ignored",
            self.parser.info().size_hint,
        )
    }

    fn visit_children<V: ParserVisitor>(&self, visitor: &mut V) {
        self.parser.visit(visitor);
    }
}

impl<'a, T, I: Input<'a>, E> Visitable for Just<T, I, E>
where
    T: OrderedSeq<'a, I::Token>,
{
    fn info(&self) -> ParserInfo<'_, Self> {
        let size = self.seq.seq_iter()
            .fold(0, |idx, _| idx + 1);
        ParserInfo::new(
            self,
            "just",
            SizeHint::new(size, Some(size))
        )
    }
}

impl<A, B> Visitable for Or<A, B>
where
    A: Visitable,
    B: Visitable,
{
    fn info(&self) -> ParserInfo<'_, Self> {
        ParserInfo::new(
            self,
            "or",
            SizeHint::or(
                self.choice.parsers.0.info().size_hint,
                self.choice.parsers.1.info().size_hint,
            )
        )
    }

    fn visit_children<V: ParserVisitor>(&self, visitor: &mut V) {
        self.choice.parsers.0.visit(visitor);
        self.choice.parsers.1.visit(visitor);
    }
}

impl<A> Visitable for OrNot<A>
where
    A: Visitable,
{
    fn info(&self) -> ParserInfo<'_, Self> {
        ParserInfo::new(
            self,
            "or_not",
            SizeHint::new(0, self.parser.info().size_hint.upper)
        )
    }

    fn visit_children<V: ParserVisitor>(&self, visitor: &mut V) {
        self.parser.visit(visitor);
    }
}

impl<A, OA, I, E> Visitable for Repeated<A, OA, I, E>
where
    A: Visitable,
{
    fn info(&self) -> ParserInfo<'_, Self> {
        let at_most = if self.at_most == !0 {
            None
        } else {
            Some(usize::try_from(self.at_most).unwrap_or(usize::MAX))
        };

        ParserInfo::new(
            self,
            "repeated",
            SizeHint::repeat(
                self.parser.info().size_hint,
                SizeHint::new(self.at_least, at_most)
            )
        )
    }

    fn visit_children<V: ParserVisitor>(&self, visitor: &mut V) {
        self.parser.visit(visitor);
    }
}

impl<A, B, OA, OB, I, E> Visitable for SeparatedBy<A, B, OA, OB, I, E>
where
    A: Visitable,
    B: Visitable,
{
    fn info(&self) -> ParserInfo<'_, Self> {
        let sep_size = self.separator.info().size_hint;
        let item_size = self.parser.info().size_hint;

        let at_most = if self.at_most == !0 {
            None
        } else {
            Some(usize::try_from(self.at_most).unwrap_or(usize::MAX))
        };

        let min = if self.allow_leading && self.allow_trailing {
            usize::min(sep_size.lower, item_size.lower)
        } else {
            item_size.lower
        } * self.at_least;

        let lead_trail = self.allow_leading as usize + self.allow_trailing as usize;
        let max = item_size.upper.zip(sep_size.upper)
            .zip(at_most)
            .map(|((item, sep), at_most)| {
                ((item + sep) * at_most) + sep * lead_trail
            });

        ParserInfo::new(
            self,
            "separated_by",
            SizeHint::new(min, max)
        )
    }

    fn visit_children<V: ParserVisitor>(&self, visitor: &mut V) {
        self.parser.visit(visitor);
        self.separator.visit(visitor);
    }
}

impl<A, O, C> Visitable for CollectExactly<A, O, C>
where
    A: Visitable,
{
    fn info(&self) -> ParserInfo<'_, Self> {
        ParserInfo::new(
            self,
            "collect_exactly",
            todo!(),
        )
    }

    fn visit_children<V: ParserVisitor>(&self, visitor: &mut V) {
        self.parser.visit(visitor);
    }
}

impl<A, B, OA, OB, E> Visitable for Then<A, B, OA, OB, E>
where
    A: Visitable,
    B: Visitable,
{
    fn info(&self) -> ParserInfo<'_, Self> {
        let a_info = self.parser_a.info();
        let b_info = self.parser_b.info();

        ParserInfo::new(
            self,
            "then",
            SizeHint::and(a_info.size_hint, b_info.size_hint)
        )
    }

    fn visit_children<V: ParserVisitor>(&self, visitor: &mut V) {
        self.parser_a.visit(visitor);
        self.parser_b.visit(visitor);
    }
}
