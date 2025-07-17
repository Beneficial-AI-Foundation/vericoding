// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_maxArray(a: Vec<int>) -> m: int
    requires
        a.len() >= 1
    ensures
        forall |k: int| 0 <= k < a.len() ==> m >= a.index(k),
        exists |k: int| 0 <= k < a.len() && m == a.index(k)
;

proof fn lemma_maxArray(a: Vec<int>) -> (m: int)
    requires
        a.len() >= 1
    ensures
        forall |k: int| 0 <= k < a.len() ==> m >= a.index(k),
        exists |k: int| 0 <= k < a.len() && m == a.index(k)
{
    0
}

}