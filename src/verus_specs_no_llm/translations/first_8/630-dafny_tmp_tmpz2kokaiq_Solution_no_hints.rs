// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn BinarySearch(a: Vec<int>, x: int) -> (index: int)
    requires sorted(a)
    ensures 0 <= index < a.len() ==> a[index] == x,
            index == -1 ==> forall i : int :: 0 <= i < a.len() ==> a[i] != x
{
}

}