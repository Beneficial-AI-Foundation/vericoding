// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

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