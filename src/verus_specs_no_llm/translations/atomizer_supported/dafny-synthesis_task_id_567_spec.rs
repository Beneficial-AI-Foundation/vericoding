// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn IsSorted(a: Vec<int>) -> (sorted: bool)
    requires a.len() > 0
    ensures sorted <== forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
            !sorted ==> exists|i: int, j: int| 0 <= i < j < a.len() and a[i] > a[j]
{
}

}