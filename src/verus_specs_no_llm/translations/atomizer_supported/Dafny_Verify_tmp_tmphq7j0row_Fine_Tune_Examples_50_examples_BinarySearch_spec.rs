// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn BinarySearch(a: Vec<int>, key: int) -> (n: int)
    requires forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
    ensures 0 <= n <= a.len(),
            forall|i: int| 0 <= i < n ==> a[i] < key,
            forall|i: int| n <= i < a.len() ==> key <= a[i]
{
}

}