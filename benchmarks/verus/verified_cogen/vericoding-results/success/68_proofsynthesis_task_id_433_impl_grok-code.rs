// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_greater(arr: &Vec<i32>, number: i32) -> (result: bool)

    ensures
        result == (forall|i: int| 0 <= i < arr.len() ==> number > arr[i]),
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): fixed loop invariant to use (i as int) for comparison with quantified variable, and changed proof assert to use int index for real vector access */
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            forall |j: int| 0 <= j < (i as int) ==> number > arr@[j]
        decreases arr.len() - i
    {
        proof {
            assert(arr@[i as int] == arr[i as int]);
        }
        if arr[i] >= number {
            return false;
        }
        i = i + 1;
    }
    proof {
        // At this point, i == arr.len(), so forall holds for all elements
        assert(forall |k: int| 0 <= k < arr.len() ==> number > arr@[k]);
    }
    return true;
}
// </vc-code>

}
fn main() {}