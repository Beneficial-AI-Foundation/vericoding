use vstd::prelude::*;

fn main() {}

verus! {

fn is_sorted(arr: &Vec<i32>) -> (is_sorted: bool)
    requires
        arr.len() > 0,
    ensures
        is_sorted == (forall|i: int, j: int| 0 <= i < j < arr.len() ==> (arr[i] <= arr[j])),
{
    for idx in 1..arr.len()
        invariant
            forall|i: int, j: int| 0 <= i < j < idx ==> arr[i] <= arr[j],
    {
        if arr[idx - 1] > arr[idx] {
            return false;
        }
    }
    true
}

} // verus!