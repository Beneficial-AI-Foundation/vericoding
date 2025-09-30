// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn argmax(arr: Vec<i32>) -> (result: usize)
    requires arr.len() > 0,
    ensures 
        result < arr.len(),
        forall|i: int| 0 <= i < result ==> arr[result as int] > arr[i],
        forall|i: int| result < i < arr.len() ==> arr[result as int] >= arr[i]
// </vc-spec>
// <vc-code>
{
    let mut max_idx: usize = 0;
    let mut i: usize = 1;
    
    while i < arr.len()
        invariant
            max_idx < arr.len(),
            i <= arr.len(),
            forall|j: int| 0 <= j < max_idx ==> arr[max_idx as int] > arr[j],
            forall|j: int| max_idx < j < i ==> arr[max_idx as int] >= arr[j],
        decreases arr.len() - i
    {
        if arr[i] > arr[max_idx] {
            max_idx = i;
        }
        i += 1;
    }
    
    max_idx
}
// </vc-code>


}
fn main() {}