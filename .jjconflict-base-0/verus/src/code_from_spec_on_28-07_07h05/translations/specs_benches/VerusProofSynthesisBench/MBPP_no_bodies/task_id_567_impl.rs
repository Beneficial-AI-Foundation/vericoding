use vstd::prelude::*;

verus! {

fn is_sorted(arr: &Vec<i32>) -> (is_sorted: bool)
    // pre-conditions-start
    requires
        arr.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        is_sorted == (forall|i: int, j: int| 0 <= i < j < arr.len() ==> (arr[i] <= arr[j])),
    // post-conditions-end
{
    for k in 1..arr.len()
        invariant
            forall|i: int, j: int| 0 <= i < j < k ==> arr[i] <= arr[j],
    {
        if arr[k - 1] > arr[k] {
            return false;
        }
    }
    true
}

} // verus!

fn main() {}