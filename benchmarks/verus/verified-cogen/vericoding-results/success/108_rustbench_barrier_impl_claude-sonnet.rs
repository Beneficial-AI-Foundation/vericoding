// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fixed sequence indexing to use int indices */
spec fn all_left_less_than_right(arr: &[i32], p: usize) -> bool
{
    forall|k: int, l: int| 0 <= k <= p && p < l < arr.len() ==> arr@[k] < arr@[l]
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn barrier(arr: &[i32], p: usize) -> (result: bool)
    requires
        arr.len() > 0,
        0 <= p < arr.len(),
    ensures
        result == forall|k: int, l: int| 0 <= k <= p && p < l < arr.len() ==> arr[k] < arr[l],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Fixed sequence indexing to use int indices throughout */
    let mut i = 0;
    while i <= p
        invariant
            0 <= i <= p + 1,
            forall|k: int, l: int| 0 <= k < i && p < l < arr.len() ==> arr@[k] < arr@[l],
        decreases p + 1 - i
    {
        let mut j = p + 1;
        while j < arr.len()
            invariant
                p + 1 <= j <= arr.len(),
                forall|l: int| p < l < j ==> arr@[i as int] < arr@[l],
                forall|k: int, l: int| 0 <= k < i && p < l < arr.len() ==> arr@[k] < arr@[l],
            decreases arr.len() - j
        {
            if arr[i] >= arr[j] {
                return false;
            }
            j += 1;
        }
        i += 1;
    }
    true
}
// </vc-code>

}
fn main() {}