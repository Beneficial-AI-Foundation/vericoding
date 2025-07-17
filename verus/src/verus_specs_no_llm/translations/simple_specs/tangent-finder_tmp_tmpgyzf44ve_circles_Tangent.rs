// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Tangent(r: Vec<int>, x: Vec<int>) -> b: bool
    requires
        forall |i: int, j: int| 0 <= i <= j < x.len() ==> x.index(i) <= x.index(j) // values in x will be in ascending order || empty,
        forall |i: int, j: int| (0 <= i < r.len() && 0 <= j < x.len()) ==> (r.index(i) >= 0 && x.index(j) >= 0)    // x && r will contain no negative values
    ensures
        !b ==> forall |i: int, j: int| 0 <= i< r.len() && 0 <= j < x.len() ==> r.index(i) != x.index(j),
        b ==> exists |i: int, j: int| 0 <= i< r.len() && 0 <= j < x.len() && r.index(i) == x.index(j)
;

proof fn lemma_Tangent(r: Vec<int>, x: Vec<int>) -> (b: bool)
    requires
        forall |i: int, j: int| 0 <= i <= j < x.len() ==> x.index(i) <= x.index(j) // values in x will be in ascending order || empty,
        forall |i: int, j: int| (0 <= i < r.len() && 0 <= j < x.len()) ==> (r.index(i) >= 0 && x.index(j) >= 0)    // x && r will contain no negative values
    ensures
        !b ==> forall |i: int, j: int| 0 <= i< r.len() && 0 <= j < x.len() ==> r.index(i) != x.index(j),
        b ==> exists |i: int, j: int| 0 <= i< r.len() && 0 <= j < x.len() && r.index(i) == x.index(j)
{
    false
}

}