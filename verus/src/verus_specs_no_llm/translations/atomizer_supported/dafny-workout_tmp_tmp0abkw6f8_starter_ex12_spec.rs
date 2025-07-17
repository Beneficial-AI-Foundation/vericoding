// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_FindMax(a: Vec<int>) -> max_idx: nat
    requires
        a.len() > 0
    ensures
        0 <= max_idx < a.len(),
        forall |j: int| 0 <= j < a.len() ==> a.index(max_idx) >= a.index(j)
;

proof fn lemma_FindMax(a: Vec<int>) -> (max_idx: nat)
    requires
        a.len() > 0
    ensures
        0 <= max_idx < a.len(),
        forall |j: int| 0 <= j < a.len() ==> a.index(max_idx) >= a.index(j)
{
    0
}

}