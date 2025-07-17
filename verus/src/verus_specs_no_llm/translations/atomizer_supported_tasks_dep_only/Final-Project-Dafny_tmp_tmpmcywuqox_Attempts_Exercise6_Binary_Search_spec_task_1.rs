// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_binarySearch(a: Vec<int>, val: int) -> pos:int
    requires
        a.len() > 0,
        forall |i: int, j: int| 0 <= i < j < a.len() ==> a.index(i) <= a.index(j)
    ensures
        0 <= pos < a.len() ==> a.index(pos) == val,
        pos < 0 || pos >= a.len()  ==> forall |i: int| 0 <= i < a.len() ==> a.index(i) != val
;

proof fn lemma_binarySearch(a: Vec<int>, val: int) -> (pos: int)
    requires
        a.len() > 0,
        forall |i: int, j: int| 0 <= i < j < a.len() ==> a.index(i) <= a.index(j)
    ensures
        0 <= pos < a.len() ==> a.index(pos) == val,
        pos < 0 || pos >= a.len()  ==> forall |i: int| 0 <= i < a.len() ==> a.index(i) != val
{
    0
}

}