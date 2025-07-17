// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sorted(a: Vec<int>) -> bool
    reads a
{
    0
}

spec fn spec_BinarySearch(a: Vec<int>, x: int) -> index: int
    requires
        sorted(a)
    ensures
        0 <= index < a.len() ==> a.index(index) == x,
        index == -1 ==> forall |i: int| 0 <= i < a.len() ==> a.index(i) != x
;

proof fn lemma_BinarySearch(a: Vec<int>, x: int) -> (index: int)
    requires
        sorted(a)
    ensures
        0 <= index < a.len() ==> a.index(index) == x,
        index == -1 ==> forall |i: int| 0 <= i < a.len() ==> a.index(i) != x
{
    0
}

}