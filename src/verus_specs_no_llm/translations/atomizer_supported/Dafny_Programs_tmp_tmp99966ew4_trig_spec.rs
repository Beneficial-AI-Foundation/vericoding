// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn P(x: int)
// ATOM 

predicate Q(x: int)
// SPEC 

method test()
    requires forall x {
}
    ensures Q(0) -> bool {
    
}

}