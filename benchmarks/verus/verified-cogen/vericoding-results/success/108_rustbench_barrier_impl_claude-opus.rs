// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 4): Fixed trigger syntax - triggers must be function calls or field accesses */
    if arr.len() == 1 {
        return true;
    }
    
    let mut i: usize = 0;
    while i <= p
        invariant
            i <= p + 1,
            forall|k: int| 0 <= k < i ==> forall|l: int| p < l < arr.len() ==> #[trigger] arr[k] < #[trigger] arr[l],
        decreases p - i + 1,
    {
        let mut j: usize = p + 1;
        while j < arr.len()
            invariant
                p + 1 <= j <= arr.len(),
                forall|l: int| p < l < j ==> #[trigger] arr[i as int] < #[trigger] arr[l],
            decreases arr.len() - j,
        {
            if arr[i] >= arr[j] {
                return false;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}