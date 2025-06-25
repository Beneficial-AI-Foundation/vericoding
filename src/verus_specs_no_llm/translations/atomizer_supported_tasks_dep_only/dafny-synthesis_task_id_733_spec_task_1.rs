// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn FindFirstOccurrence(arr: Vec<int>, target: int) -> (index: int)
    requires arr != null,
             forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
    ensures 0 <= index < arr.len() ==> arr[index] == target,
            index == -1 ==> forall|i: int| 0 <= i < arr.len() ==> arr[i] != target,
            forall|i: int| 0 <= i < arr.len() ==> arr[i] == old(arr[i])
{
}

}