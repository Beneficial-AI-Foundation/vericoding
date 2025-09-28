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
/* code modified by LLM (iteration 3): Fixed mismatched types by using `@` for sequence access as specified in the original ensures clause. */
{
    let mut max_idx: usize = 0;
    let mut i: usize = 1;

    while i < arr.len()
        invariant
            0 < arr.len(),
            1 <= i,
            i <= arr.len(),
            max_idx < i,
            max_idx < arr.len(),
            // For all elements encountered so far, they are less than or equal to the element at max_idx
            forall|k: int| 0 <= k && k < i ==> arr@[k] <= arr@[max_idx as int],
            // Additionally, for indices before max_idx, they are strictly less than the element at max_idx
            // This helps in finding the *first* argmax in case of ties
            forall|k: int| 0 <= k && k < max_idx as int ==> arr@[k] < arr@[max_idx as int],
        decreases arr.len() - i
    {
        if arr[i] > arr[max_idx]
        {
            max_idx = i;
        }

        i = i + 1;
    }

    max_idx
}
// </vc-code>

}
fn main() {}