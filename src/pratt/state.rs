use std::marker::PhantomData;

use crate::private;

/// DOC
pub struct Infix<P, PO> {
    pub(crate) infix: P,
    pub(crate) phantom: PhantomData<PO>,
}

/// DOC
pub struct InfixPrefix<P1, P1O, P2, P2O> {
    pub(crate) infix: P1,
    pub(crate) prefix: P2,
    pub(crate) phantom: PhantomData<(P1O, P2O)>,
}

/// DOC
pub trait PrattOps: private::Sealed {}

impl<P, PO> private::Sealed for Infix<P, PO> {}

impl<P1, P2, P1O, P2O> private::Sealed for InfixPrefix<P1, P2, P1O, P2O> {}

impl<P, PO> PrattOps for Infix<P, PO> {}

impl<P1, P2, P1O, P2O> PrattOps for InfixPrefix<P1, P2, P1O, P2O> {}
