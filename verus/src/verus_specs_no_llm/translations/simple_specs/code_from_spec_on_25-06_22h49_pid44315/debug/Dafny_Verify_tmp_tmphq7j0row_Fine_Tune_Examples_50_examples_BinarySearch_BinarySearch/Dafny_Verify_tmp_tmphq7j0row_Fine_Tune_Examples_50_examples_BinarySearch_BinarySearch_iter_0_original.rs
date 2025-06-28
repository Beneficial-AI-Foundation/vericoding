// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn BinarySearch(a: Vec<int>, key: int) -> (n: int)
    requires
        forall i, j :: 0 <= i < j < a.len() ==> a.spec_index(i) <= a.spec_index(j)
    ensures
        0 <= n <= a.len(),
        forall i :: 0 <= i < n ==> a.spec_index(i) < key,
        forall i :: n <= i < a.len() ==> key <= a.spec_index(i)
{
    return 0;
}

}