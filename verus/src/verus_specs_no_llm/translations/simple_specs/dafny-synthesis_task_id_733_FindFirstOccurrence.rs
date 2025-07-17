// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_FindFirstOccurrence(arr: Vec<int>, target: int) -> index: int
    requires
        arr != null,
        forall |i: int, j: int| 0 <= i < j < arr.len() ==> arr.index(i) <= arr.index(j)
    ensures
        0 <= index < arr.len() ==> arr.index(index) == target,
        index == -1 ==> forall |i: int| 0 <= i < arr.len() ==> arr.index(i) != target,
        forall |i: int| 0 <= i < arr.len() ==> arr.index(i) == old(arr.index(i))
;

proof fn lemma_FindFirstOccurrence(arr: Vec<int>, target: int) -> (index: int)
    requires
        arr != null,
        forall |i: int, j: int| 0 <= i < j < arr.len() ==> arr.index(i) <= arr.index(j)
    ensures
        0 <= index < arr.len() ==> arr.index(index) == target,
        index == -1 ==> forall |i: int| 0 <= i < arr.len() ==> arr.index(i) != target,
        forall |i: int| 0 <= i < arr.len() ==> arr.index(i) == old(arr.index(i))
{
    0
}

}