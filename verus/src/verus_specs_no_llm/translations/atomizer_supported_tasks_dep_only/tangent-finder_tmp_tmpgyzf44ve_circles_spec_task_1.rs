// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

fn Tangent(r: Vec<int>, x: Vec<int>) -> (b: bool)
    requires
        forall i, j :: 0 <= i <= j < x.len() ==> x.spec_index(i) <= x.spec_index(j) // values in x will be in ascending order || empty,
        forall i, j :: (0 <= i < r.len() && 0 <= j < x.len()) ==> (r.spec_index(i) >= 0 && x.spec_index(j) >= 0)       // x && r will contain no negative values
    ensures
        !b ==> forall i, j :: 0 <= i< r.len() && 0 <= j < x.len() ==> r.spec_index(i) != x.spec_index(j),
        b ==> exists i, j :: 0 <= i< r.len() && 0 <= j < x.len() && r.spec_index(i) == x.spec_index(j)
{
    return false;
}

}