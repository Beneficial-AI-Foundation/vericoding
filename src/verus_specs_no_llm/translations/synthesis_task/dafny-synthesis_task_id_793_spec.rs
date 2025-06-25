// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn LastPosition(arr: Vec<int>, elem: int) -> (pos: int)
    requires arr.len() > 0,
             forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
    ensures pos == -1 | (0 <= pos < arr.len() and arr[pos] == elem and (pos <= arr.len() - 1 .len()| arr[pos + 1] > elem)),
            forall|i: int| 0 <= i < arr.len() ==> arr[i] == old(arr[i])
{
}

}