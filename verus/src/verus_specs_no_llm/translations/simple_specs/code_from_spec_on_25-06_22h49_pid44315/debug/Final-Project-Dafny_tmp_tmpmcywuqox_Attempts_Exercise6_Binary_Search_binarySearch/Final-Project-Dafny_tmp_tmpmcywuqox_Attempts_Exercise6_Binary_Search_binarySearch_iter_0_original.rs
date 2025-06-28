// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn binarySearch(a: Vec<int>, val: int) -> (pos: int)
    requires
        a.len() > 0,
        forall i, j :: 0 <= i < j < a.len() ==> a.spec_index(i) <= a.spec_index(j)
    ensures
        0 <= pos < a.len() ==> a.spec_index(pos) == val,
        pos < 0 || pos >= a.len() ==> forall i :: 0 <= i < a.len() ==> a.spec_index(i) != val
{
    return 0;
}

}