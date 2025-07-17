// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_MaxDifference(a: Vec<int>) -> diff: int
    requires
        a.len() > 1
    ensures
        forall |i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a.index(i) - a.index(j) <= diff
;

proof fn lemma_MaxDifference(a: Vec<int>) -> (diff: int)
    requires
        a.len() > 1
    ensures
        forall |i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a.index(i) - a.index(j) <= diff
{
    0
}

}