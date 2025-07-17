// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_IsSorted(a: Vec<int>) -> sorted: bool
    requires
        a.len() > 0
    ensures
        sorted <== forall |i: int, j: int| 0 <= i < j < a.len() ==> a.index(i) <= a.index(j),
        !sorted ==> exists |i: int, j: int| 0 <= i < j < a.len() && a.index(i) > a.index(j)
;

proof fn lemma_IsSorted(a: Vec<int>) -> (sorted: bool)
    requires
        a.len() > 0
    ensures
        sorted <== forall |i: int, j: int| 0 <= i < j < a.len() ==> a.index(i) <= a.index(j),
        !sorted ==> exists |i: int, j: int| 0 <= i < j < a.len() && a.index(i) > a.index(j)
{
    false
}

}