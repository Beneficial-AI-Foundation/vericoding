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
    
    // Check all pairs: left partition elements vs right partition elements
    for i in 0..=p
        invariant
            forall|k: int, l: int| 0 <= k < i && p < l < arr.len() ==> arr[k] < arr[l],
    {
        for j in (p + 1)..arr.len()
            invariant
                forall|k: int, l: int| 0 <= k < i && p < l < arr.len() ==> arr[k] < arr[l],
                forall|l: int| (p + 1) <= l < j ==> arr[i] < arr[l],
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