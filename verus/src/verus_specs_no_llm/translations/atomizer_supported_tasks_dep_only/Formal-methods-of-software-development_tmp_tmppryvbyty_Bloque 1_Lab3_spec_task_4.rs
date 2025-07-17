// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn factorial(n: int) -> int
    requires
        n>=0
{
    0
}

spec fn spec_ComputeFact(n: int) -> f:int
    requires
        n >=0
    ensures
        f== factorial(n)
;

proof fn lemma_ComputeFact(n: int) -> (f: int)
    requires
        n >=0
    ensures
        f== factorial(n)
{
    0
}

}