// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn KthElement(arr: Vec<int>, k: int) -> (result: int)
    requires
        1 <= k <= arr.len()
    ensures
        result == arr.spec_index(k - 1)
{
    return 0;
}

}