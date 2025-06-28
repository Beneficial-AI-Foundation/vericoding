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
    let idx = (k - 1) as usize;
    arr[idx]
}

}