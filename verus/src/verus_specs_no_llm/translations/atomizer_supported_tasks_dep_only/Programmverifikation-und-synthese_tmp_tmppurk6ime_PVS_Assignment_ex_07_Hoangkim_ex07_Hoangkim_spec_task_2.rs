// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_FindMin(a: Vec<int>, lo: nat) -> minIdx: nat
    requires
        a != null && a.len() > 0 && lo < a.len()
    ensures
        lo <= minIdx < a.len(),
        forall |x: int| lo <= x < a.len() ==> a.index(minIdx) <= a.index(x)
;

proof fn lemma_FindMin(a: Vec<int>, lo: nat) -> (minIdx: nat)
    requires
        a != null && a.len() > 0 && lo < a.len()
    ensures
        lo <= minIdx < a.len(),
        forall |x: int| lo <= x < a.len() ==> a.index(minIdx) <= a.index(x)
{
    0
}

}