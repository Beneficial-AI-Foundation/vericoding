// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_FindMedian(a: Vec<int>, b: Vec<int>) -> median: int
    requires
        a != null && b != null,
        a.len() == b.len(),
        a.len() > 0,
        forall |i: int| 0 <= i < a.len() - 1 ==> a.index(i) <= a.index(i + 1),
        forall |i: int| 0 <= i < b.len() - 1 ==> b.index(i) <= b.index(i + 1)
    ensures
        median == if (a.len() % 2 == 0) then (a.index(a.len() / 2 - 1) + b.index(0)) / 2 else a.index(a.len() / 2)
;

proof fn lemma_FindMedian(a: Vec<int>, b: Vec<int>) -> (median: int)
    requires
        a != null && b != null,
        a.len() == b.len(),
        a.len() > 0,
        forall |i: int| 0 <= i < a.len() - 1 ==> a.index(i) <= a.index(i + 1),
        forall |i: int| 0 <= i < b.len() - 1 ==> b.index(i) <= b.index(i + 1)
    ensures
        median == if (a.len() % 2 == 0) then (a.index(a.len() / 2 - 1) + b.index(0)) / 2 else a.index(a.len() / 2)
{
    0
}

}