// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_min(a: Vec<int>, n: int) -> min : int
    requires
        0 < n <= a.len()
    ensures
        (exists |i: int| 0 <= i && i < n && a.index(i) == min),
        (forall |i: int| 0 <= i && i < n ==> a.index(i) >= min)
;

proof fn lemma_min(a: Vec<int>, n: int) -> (min: int)
    requires
        0 < n <= a.len()
    ensures
        (exists |i: int| 0 <= i && i < n && a.index(i) == min),
        (forall |i: int| 0 <= i && i < n ==> a.index(i) >= min)
{
    0
}

}