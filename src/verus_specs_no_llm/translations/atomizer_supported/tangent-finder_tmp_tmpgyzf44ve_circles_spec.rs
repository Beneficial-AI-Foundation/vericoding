// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Tangent(r: Vec<int>, x: Vec<int>) -> (b: bool)
    requires forall|i: int, j: int| 0 <= i <= j < x.len() ==> x[i] <= x[j] // values in x will be in ascending order or empty,
             forall|i: int, j: int| (0 <= i < r.len() and 0 <= j < x.len()) ==> (r[i] >= 0 and x[j] >= 0)       // x and r will contain no negative values
    ensures !b ==> forall|i: int, j: int| 0 <= i< r.len() and 0 <= j < x.len() ==> r[i] != x[j],
            b ==> exists|i: int, j: int| 0 <= i< r.len() and 0 <= j < x.len() and r[i] == x[j]
{
}

}