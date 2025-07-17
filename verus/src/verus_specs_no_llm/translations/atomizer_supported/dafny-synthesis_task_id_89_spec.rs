// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_ClosestSmaller(n: int) -> m: int
    requires
        n > 0
    ensures
        m + 1 == n
;

proof fn lemma_ClosestSmaller(n: int) -> (m: int)
    requires
        n > 0
    ensures
        m + 1 == n
{
    0
}

}