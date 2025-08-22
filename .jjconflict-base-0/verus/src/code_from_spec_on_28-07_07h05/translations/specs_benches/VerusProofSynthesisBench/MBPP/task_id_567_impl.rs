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
    let mut k = 0;
    while k < arr.len() - 1
        invariant
            0 <= k <= arr.len() - 1,
            forall|i: int, j: int| 0 <= i < j < k + 1 ==> arr[i] <= arr[j],
        /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
        decreases arr.len() - 1 - k
    {
        if arr[k] > arr[k + 1] {
            return false;
        }
        k += 1;
    }
    true
}

} // verus!

fn main() {}