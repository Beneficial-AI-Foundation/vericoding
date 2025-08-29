use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-description>
/*
function_signature: "fn barrier(arr: &[i32], p: usize) -> (result: bool)"
docstring: Implement barrier functionality.
*/
// </vc-description>

// <vc-spec>
fn barrier(arr: &[i32], p: usize) -> (result: bool)
    requires p < arr.len()
    ensures result == (forall|i: int| 0 <= i < p ==> arr@[i] <= arr@[p as int]) &&
            (forall|i: int| p < i < arr.len() ==> arr@[i] >= arr@[p as int])
// </vc-spec>

// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed for loop syntax by adding proper braces around invariant clauses */
    let pivot_val = arr[p];
    
    for i in 0..p
        invariant 
            forall|j: int| 0 <= j < i ==> arr@[j] <= pivot_val,
            i <= p,
    {
        if arr[i] > pivot_val {
            return false;
        }
    }
    
    for i in (p + 1)..arr.len()
        invariant 
            forall|j: int| p < j < i ==> arr@[j] >= pivot_val,
            p < i <= arr.len(),
    {
        if arr[i] < pivot_val {
            return false;
        }
    }
    
    true
}
// </vc-code>

fn main() {}
}