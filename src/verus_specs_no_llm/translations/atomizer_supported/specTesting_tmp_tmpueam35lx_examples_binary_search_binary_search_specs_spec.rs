// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn BinarySearchTransition(intSeq: Seq<int>, key: int, r: int)
    requires (forall i, j | 0 <= i <= j < |intSeq|: : intSeq[i] <= intSeq[j]) -> bool {
    and (r >= 0 ==> r < intSeq.len() and intSeq[r] == key)
    and (r < 0 ==> forall i:nat  i < .len()intSeq| :: intSeq[i] != key)
}

spec fn BinarySearchDeterministicTransition(intSeq: Seq<int>, key: int, r: int)
    requires (forall i, j | 0 <= i <= j < |intSeq|: : intSeq[i] <= intSeq[j]) -> bool {
    and (r >= 0 ==> r < intSeq.len() and intSeq[r] == key)
    and (r < 0 ==> forall i:nat  i < .len()intSeq :: intSeq[i] != key)

    // make it deterministic
    and (r < 0 ==> r == -1) // return -1 if not found
    and (r >= 0 ==> forall i:nat .len() i < r :: intSeq[i] < key)
}

}