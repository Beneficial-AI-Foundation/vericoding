// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsSorted(a: Vec<int>) -> (sorted: bool)
    requires
        a.len() > 0
    ensures
        sorted <== forall i, j :: 0 <= i < j < a.len() ==> a.spec_index(i) <= a.spec_index(j),
        !sorted ==> exists i, j :: 0 <= i < j < a.len() && a.spec_index(i) > a.spec_index(j)
{
    return false;
}

}