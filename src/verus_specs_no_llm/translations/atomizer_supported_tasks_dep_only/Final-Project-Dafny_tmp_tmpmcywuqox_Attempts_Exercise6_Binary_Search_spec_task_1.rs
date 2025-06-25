// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn binarySearch(a: Vec<int>, val: int) -> (pos: int)
    requires a.len() > 0,
             forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
    ensures 0 <= pos < a.len() ==> a[pos] == val,
            pos < 0 or pos >= a.len()  ==> forall|i: int| 0 <= i < a.len() ==> a[i] != val
{
}

}