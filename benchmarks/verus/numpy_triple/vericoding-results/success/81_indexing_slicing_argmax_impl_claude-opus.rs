// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn argmax(arr: &Vec<i8>) -> (result: usize)
    requires arr.len() > 0,
    ensures 
        result < arr.len(),
        forall|i: int| 0 <= i && i < arr.len() ==> arr@[i] <= arr@[result as int],
        forall|i: int| 0 <= i && i < result as int ==> arr@[i] < arr@[result as int],
        forall|i: int| (result as int) < i && i < arr.len() ==> arr@[i] <= arr@[result as int],
// </vc-spec>
// <vc-code>
{
    let mut max_idx: usize = 0;
    let mut max_val: i8 = arr[0];
    let mut i: usize = 1;
    
    while i < arr.len()
        invariant
            0 <= max_idx < arr.len(),
            0 < i <= arr.len(),
            max_val == arr@[max_idx as int],
            forall|j: int| 0 <= j && j < i ==> arr@[j] <= max_val,
            forall|j: int| 0 <= j && j < max_idx as int ==> arr@[j] < max_val,
        decreases arr.len() - i
    {
        if arr[i] > max_val {
            max_val = arr[i];
            max_idx = i;
        }
        i = i + 1;
    }
    
    max_idx
}
// </vc-code>

}
fn main() {}