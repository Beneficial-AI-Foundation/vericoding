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
    /* code modified by LLM (iteration 4): Fixed type mismatches by using usize for exec indices and removing casts. */
    let mut idx: usize = 0;
    let mut i: usize = 1;
    while i < arr.len()
        invariant
            0 <= idx as int,
            (idx as int) < i as int,
            (i as int) <= arr.len() as int,
            forall|j: int| 0 <= j && j < i as int ==> arr@[j] <= arr@[idx as int],
            forall|j: int| 0 <= j && j < idx as int ==> arr@[j] < arr@[idx as int],
        decreases (arr.len() as int) - (i as int)
    {
        if arr[i] > arr[idx] {
            idx = i;
        }
        i = i + 1;
    }
    idx
}
// </vc-code>

}
fn main() {}