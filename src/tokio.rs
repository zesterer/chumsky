use super::*;

use bytes::Bytes;

impl<'src> Input<'src> for Bytes {
    type Cursor = usize;
    type Span = SimpleSpan<usize>;

    type Token = u8;
    type MaybeToken = u8;

    type Cache = Self;

    #[inline]
    fn begin(self) -> (Self::Cursor, Self::Cache) {
        (0, self)
    }

    #[inline]
    fn cursor_location(cursor: &Self::Cursor) -> usize {
        *cursor
    }

    #[inline(always)]
    unsafe fn next_maybe(
        this: &mut Self::Cache,
        cursor: &mut Self::Cursor,
    ) -> Option<Self::MaybeToken> {
        if let Some(tok) = this.get(*cursor) {
            *cursor += 1;
            Some(*tok)
        } else {
            None
        }
    }

    #[inline(always)]
    unsafe fn span(_this: &mut Self::Cache, range: Range<&Self::Cursor>) -> Self::Span {
        (*range.start..*range.end).into()
    }
}

impl<'src> ExactSizeInput<'src> for Bytes {
    #[inline(always)]
    unsafe fn span_from(this: &mut Self::Cache, range: RangeFrom<&Self::Cursor>) -> Self::Span {
        (*range.start..this.len()).into()
    }
}

impl Sealed for Bytes {}
impl<'src> StrInput<'src> for Bytes {
    #[doc(hidden)]
    fn stringify(slice: Self::Slice) -> String {
        slice
            .iter()
            // .map(|e| core::ascii::Char::from_u8(e).unwrap_or(AsciiChar::Substitute).to_char())
            .map(|e| char::from(*e))
            .collect()
    }
}

impl<'src> SliceInput<'src> for Bytes {
    type Slice = Bytes;

    #[inline(always)]
    fn full_slice(this: &mut Self::Cache) -> Self::Slice {
        this.clone()
    }

    #[inline(always)]
    unsafe fn slice(this: &mut Self::Cache, range: Range<&Self::Cursor>) -> Self::Slice {
        this.slice(*range.start..*range.end)
    }

    #[inline(always)]
    unsafe fn slice_from(this: &mut Self::Cache, from: RangeFrom<&Self::Cursor>) -> Self::Slice {
        this.slice(*from.start..)
    }
}

impl<'src> ValueInput<'src> for Bytes {
    #[inline(always)]
    unsafe fn next(this: &mut Self::Cache, cursor: &mut Self::Cursor) -> Option<Self::Token> {
        Self::next_maybe(this, cursor)
    }
}
