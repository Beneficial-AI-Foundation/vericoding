use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn barrier(arr: &[i32], p: usize) -> (result: bool)
    requires
        arr.len() > 0,
        0 <= p < arr.len(),
    ensures
        result == forall|k: int, l: int| 0 <= k <= p && p < l < arr.len() ==> arr[k] < arr[l],
{
    let mut k: usize = 0;
    while k <= p
        invariant
            0 <= k <= p + 1,
            forall|k2: int, l: int| 0 <= k2 < k && p < l < arr.len() ==> arr[k2] < arr[l],
        /* code modified by LLM (iteration 1): added decreases clause to fix verification error */
        decreases p + 1 - k
    {
        let mut l: usize = p + 1;
        while l < arr.len()
            invariant
                p + 1 <= l <= arr.len(),
                forall|l2: int| p < l2 < l ==> arr[k as int] < arr[l2],
                forall|k2: int, l2: int| 0 <= k2 < k && p < l2 < arr.len() ==> arr[k2] < arr[l2],
            decreases arr.len() - l
        {
            if arr[k] >= arr[l] {
                return false;
            }
            l += 1;
        }
        k += 1;
    }
    true
}

fn main() {}
}