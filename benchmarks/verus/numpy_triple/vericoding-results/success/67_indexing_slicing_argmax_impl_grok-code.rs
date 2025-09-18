// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn argmax(arr: &Vec<i32>) -> (result: usize)
    requires arr.len() > 0,
    ensures 
        result < arr.len(),
        forall|i: int| 0 <= i && i < arr.len() ==> arr@[i] <= arr@[result as int],
        forall|i: int| 0 <= i && i < result as int ==> arr@[i] < arr@[result as int],
        forall|i: int| (result as int) < i && i < arr.len() ==> arr@[i] <= arr@[result as int],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed invariant with proper int types and bounds */
    let mut max_i: usize = 0;
    let mut max_val = arr[0];
    let mut i: usize = 1;
    while i < arr.len()
        invariant
            0 <= max_i && max_i < arr.len(),
            0 <= i && i <= arr.len(),
            max_val == arr@[max_i as int],
            forall|k: int| 0 <= k && k < i ==> arr@[k] <= max_val,
            forall|k: int| 0 <= k && k < max_i ==> arr@[k] < max_val,
            decreases (arr.len() as int - i as int),
    {
        let val = arr[i];
        if val > max_val {
            max_i = i;
            max_val = val;
        }
        i += 1;
    }
    max_i
}
// </vc-code>

}
fn main() {}