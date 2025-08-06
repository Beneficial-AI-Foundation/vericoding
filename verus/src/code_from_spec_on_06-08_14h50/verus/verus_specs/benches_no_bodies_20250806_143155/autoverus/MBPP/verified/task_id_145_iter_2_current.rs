use vstd::prelude::*;

fn main() {
}

verus! {

fn max_difference(arr: &Vec<i32>) -> (diff: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
    ensures
        forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() ==> arr[i] - arr[j] <= diff,
{
    let mut max_val = arr[0];
    let mut min_val = arr[0];
    
    let mut idx = 1;
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while idx < arr.len()
        invariant
            1 <= idx <= arr.len(),
            forall|k: int| 0 <= k < idx ==> arr[k] <= max_val,
            forall|k: int| 0 <= k < idx ==> min_val <= arr[k],
            i32::MIN / 2 < max_val < i32::MAX / 2,
            i32::MIN / 2 < min_val < i32::MAX / 2,
        decreases arr.len() - idx,
    {
        if arr[idx as usize] > max_val {
            max_val = arr[idx as usize];
        }
        if arr[idx as usize] < min_val {
            min_val = arr[idx as usize];
        }
        idx += 1;
    }
    
    max_val - min_val
}

} // verus!