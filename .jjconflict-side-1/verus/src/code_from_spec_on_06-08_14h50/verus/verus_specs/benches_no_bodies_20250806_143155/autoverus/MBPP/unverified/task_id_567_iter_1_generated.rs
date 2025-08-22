use vstd::prelude::*;

fn main() {}

verus! {

fn is_sorted(arr: &Vec<i32>) -> (is_sorted: bool)
    requires
        arr.len() > 0,
    ensures
        is_sorted == (forall|i: int, j: int| 0 <= i < j < arr.len() ==> (arr[i] <= arr[j])),
{
    let mut idx = 0;
    while idx < arr.len() - 1
        invariant
            0 <= idx <= arr.len() - 1,
            forall|i: int, j: int| 0 <= i < j <= idx ==> arr[i] <= arr[j],
    {
        if arr[idx] > arr[idx + 1] {
            return false;
        }
        idx += 1;
    }
    true
}

} // verus!