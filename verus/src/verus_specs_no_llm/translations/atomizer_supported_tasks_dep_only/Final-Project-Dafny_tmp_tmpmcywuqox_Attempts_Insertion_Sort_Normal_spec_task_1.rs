// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_lookForMin(a: Vec<int>, i: int) -> m: int
    requires
        0 <= i < a.len()
    ensures
        i <= m < a.len(),
        forall |k: int| i <= k < a.len() ==> a.index(k) >= a.index(m)
;

proof fn lemma_lookForMin(a: Vec<int>, i: int) -> (m: int)
    requires
        0 <= i < a.len()
    ensures
        i <= m < a.len(),
        forall |k: int| i <= k < a.len() ==> a.index(k) >= a.index(m)
{
    0
}

}