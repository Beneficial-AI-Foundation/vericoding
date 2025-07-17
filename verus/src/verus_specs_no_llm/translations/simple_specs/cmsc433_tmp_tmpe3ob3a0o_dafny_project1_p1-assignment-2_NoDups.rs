// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_NoDups(a: Vec<int>) -> noDups : bool
    requires
        forall |j: int| 0 < j < a.len() ==> a.index(j-1) <= a.index(j) // a sorted
    ensures
        noDups <==> forall |j: int| 1 <= j < a.len() ==> a.index(j-1) != a.index(j)
;

proof fn lemma_NoDups(a: Vec<int>) -> (noDups: bool)
    requires
        forall |j: int| 0 < j < a.len() ==> a.index(j-1) <= a.index(j) // a sorted
    ensures
        noDups <==> forall |j: int| 1 <= j < a.len() ==> a.index(j-1) != a.index(j)
{
    false
}

}