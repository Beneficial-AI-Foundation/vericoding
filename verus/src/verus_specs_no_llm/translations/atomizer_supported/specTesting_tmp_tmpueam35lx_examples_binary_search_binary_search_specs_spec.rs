// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn BinarySearchTransition(intSeq: Seq<int>, key: int, r: int)
    requires (forall i, j | 0 <= i <= j < |intSeq|: : intSeq[i] <= intSeq[j]) -> bool {
    && (r >= 0 ==> r < intSeq.len() && intSeq.index(r) == key)
    && (r < 0 ==> forall i:nat  i < .len()intSeq| :: intSeq.index(i) != key)
}
spec fn BinarySearchDeterministicTransition(intSeq: Seq<int>, key: int, r: int)
    requires (forall i, j | 0 <= i <= j < |intSeq|: : intSeq[i] <= intSeq[j]) -> bool {
    && (r >= 0 ==> r < intSeq.len() && intSeq.index(r) == key)
    && (r < 0 ==> forall |i: nat  i < .len()intSeq| intSeq.index(i) != key)

    // make it deterministic
    && (r < 0 ==> r == -1) // return -1 if not found
    && (r >= 0 ==> forall |i: nat .len() i < r| intSeq.index(i) < key)
}

}