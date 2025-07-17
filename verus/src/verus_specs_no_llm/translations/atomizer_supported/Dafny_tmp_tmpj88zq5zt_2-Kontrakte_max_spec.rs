// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_max(a: Vec<int>, b: Vec<int>, i: int, j: int) -> m: int
    requires
        0 <= i < a.len(),
        0 <= j < b.len()
    ensures
        a.index(i) > b.index(j) ==> m == a.index(i),
        a.index(i) <= b.index(j) ==> m == b.index(j)
;

proof fn lemma_max(a: Vec<int>, b: Vec<int>, i: int, j: int) -> (m: int)
    requires
        0 <= i < a.len(),
        0 <= j < b.len()
    ensures
        a.index(i) > b.index(j) ==> m == a.index(i),
        a.index(i) <= b.index(j) ==> m == b.index(j)
{
    0
}

}