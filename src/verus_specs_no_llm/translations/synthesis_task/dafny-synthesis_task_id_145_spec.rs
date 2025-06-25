// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn MaxDifference(a: Vec<int>) -> (diff: int)
    requires a.len() > 1
    ensures forall|i: int, j: int| 0 <= i < a.len() and 0 <= j < a.len() ==> a[i] - a[j] <= diff
{
}

}