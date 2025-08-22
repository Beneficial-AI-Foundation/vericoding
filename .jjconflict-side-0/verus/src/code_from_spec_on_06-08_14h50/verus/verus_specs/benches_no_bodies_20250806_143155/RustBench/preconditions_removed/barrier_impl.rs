#![crate_name="barrier"]

use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn barrier(arr: &[i32], p: usize) -> (result: bool)
    ensures
        result == forall|k: int, l: int| 0 <= k <= p && p < l < arr.len() ==> arr[k] < arr[l],
{
    // Handle edge cases
    if p >= arr.len() || p + 1 >= arr.len() {
        return true;
    }
    
    /* code modified by LLM (iteration 1): Changed from 0..=p to 0..(p+1) since RangeInclusive is not supported, and fixed type conversions */
    // Check all pairs: left partition elements vs right partition elements
    for i in 0..(p + 1)
        invariant
            forall|k: int, l: int| 0 <= k < i && p < l < arr.len() ==> arr[k as int] < arr[l],
    {
        for j in (p + 1)..arr.len()
            invariant
                forall|k: int, l: int| 0 <= k < i && p < l < arr.len() ==> arr[k as int] < arr[l],
                forall|l: int| (p + 1) <= l < j ==> arr[i as int] < arr[l],
        {
            if arr[i] >= arr[j] {
                return false;
            }
        }
    }
    
    true
}

fn main() {}
}