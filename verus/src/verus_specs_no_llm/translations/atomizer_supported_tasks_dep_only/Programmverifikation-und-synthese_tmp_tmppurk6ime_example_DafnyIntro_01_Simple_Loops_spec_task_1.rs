// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Gauss(n: int) -> sum:int
    requires
        n >= 0
    ensures
        sum == n*(n+1)/2     //
;

proof fn lemma_Gauss(n: int) -> (sum: int)
    requires
        n >= 0
    ensures
        sum == n*(n+1)/2     //
{
    0
}

}