use vstd::prelude::*;

verus! {

//IMPL max_difference
/* code modified by LLM (iteration 4): Fixed function signature, moved requires/ensures inside function body, and fixed return type */
fn max_difference(arr: &Vec<i32>) -> (diff: i32)
{
    return false;  // TODO: Remove this line and implement the function body
}
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
    /* code modified by LLM (iteration 4): implemented proper algorithm to find maximum difference */
    let mut max_val = arr[0];
    let mut min_val = arr[0];
    
    let mut k = 1;
    while k < arr.len()
        invariant
            0 <= k <= arr.len(),
            forall|i: int| 0 <= i < k ==> arr[i] <= max_val,
            forall|i: int| 0 <= i < k ==> min_val <= arr[i],
            exists|i: int| 0 <= i < k && arr[i] == max_val,
            exists|i: int| 0 <= i < k && arr[i] == min_val,
    {
        if arr[k] > max_val {
            max_val = arr[k];
        }
        if arr[k] < min_val {
            min_val = arr[k];
        }
        k += 1;
    }
    
    max_val - min_val
}

} // verus!

fn main() {}