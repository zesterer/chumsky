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
pub struct InfixPostfix<P1, P1O, P2, P2O> {
    pub(crate) infix: P1,
    pub(crate) postfix: P2,
    pub(crate) phantom: PhantomData<(P1O, P2O)>,
}

/// DOC
pub struct InfixPrefixPostfix<P1, P1O, P2, P2O, P3, P3O> {
    pub(crate) infix: P1,
    pub(crate) prefix: P2,
    pub(crate) postfix: P3,
    pub(crate) phantom: PhantomData<(P1O, P2O, P3O)>,
}
