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
    let mut i: usize = 1;
    while i < arr.len()
        invariant
            1 <= i <= arr.len(),
            0 <= max_idx < i,
            forall|k: int| 0 <= k < i ==> arr@[k] <= arr@[max_idx as int],
            forall|k: int| 0 <= k < (max_idx as int) ==> arr@[k] < arr@[max_idx as int],
        decreases arr.len() - i
    {
        if arr[i] > arr[max_idx] {
            max_idx = i;
        }
        i = i + 1;
    }
    max_idx
}
// </vc-code>

}
fn main() {}