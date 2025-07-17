// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_IsSorted(a: Vec<int>) -> isSorted : bool
    ensures
        isSorted <==> forall |j: int| 1 <= j < a.len() ==> a.index(j-1) <= a.index(j)
;

proof fn lemma_IsSorted(a: Vec<int>) -> (isSorted: bool)
    ensures
        isSorted <==> forall |j: int| 1 <= j < a.len() ==> a.index(j-1) <= a.index(j)
{
    false
}

}