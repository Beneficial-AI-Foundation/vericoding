use vstd::prelude::*;

verus! {

fn max_difference(arr: &Vec<i32>) -> (diff: i32)
    // pre-conditions-start
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() ==> arr[i] - arr[j] <= diff,
    // post-conditions-end
{
    let mut max_val = arr[0];
    let mut min_val = arr[0];
    
    let mut idx = 1;
    while idx < arr.len()
        invariant
            1 <= idx <= arr.len(),
            forall|k: int| 0 <= k < idx ==> arr[k] <= max_val,
            forall|k: int| 0 <= k < idx ==> min_val <= arr[k],
            exists|k: int| 0 <= k < idx && arr[k] == max_val,
            exists|k: int| 0 <= k < idx && arr[k] == min_val,
        /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
        decreases arr.len() - idx
    {
        if arr[idx] > max_val {
            max_val = arr[idx];
        }
        if arr[idx] < min_val {
            min_val = arr[idx];
        }
        idx += 1;
    }
    
    max_val - min_val
}

} // verus!


fn main() {}