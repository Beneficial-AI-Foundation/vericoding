// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn KthElement(arr: Vec<int>, k: int) -> (result: int)
    requires 1 <= k <= arr.len()
    ensures result == arr[k - 1]
{
}

}