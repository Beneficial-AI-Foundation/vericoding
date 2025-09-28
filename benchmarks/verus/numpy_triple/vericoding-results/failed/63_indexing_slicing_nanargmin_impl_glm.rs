// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn f32_is_nan(x: f32) -> bool;
spec fn f32_le(a: f32, b: f32) -> bool;
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn nanargmin(a: Vec<f32>) -> (result: usize)
    requires 
        a.len() > 0,
        exists|i: int| 0 <= i < a.len() && !f32_is_nan(a[i]),
    ensures
        result < a.len(),
        !f32_is_nan(a[result as int]),
        forall|j: int| 0 <= j < a.len() && !f32_is_nan(a[j]) ==> f32_le(a[result as int], a[j]),
        forall|j: int| 0 <= j < a.len() && !f32_is_nan(a[j]) && f32_le(a[j], a[result as int]) && f32_le(a[result as int], a[j]) ==> result as int <= j,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): added proof blocks to assert invariants after min_index update */
{
    let mut min_index = 0;
    let mut i = 0;
    // Skip all NaNs at the beginning
    while i < a.len() && a[i] != a[i]
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> f32_is_nan(a[j]),
        decreases a.len() - i
    {
        i += 1;
    }
    // Now, if we found a non-NaN, set min_index to i and then start the second loop from i+1.
    if i < a.len() {
        min_index = i;
    } else {
        // By precondition, there is at least one non-NaN, so we should have found one.
        assert(false);
    }
    let mut j = i + 1;
    while j < a.len()
        invariant
            i+1 <= j <= a.len(),
            min_index < a.len(),
            !f32_is_nan(a[min_index as int]),
            forall|k: int| 0 <= k < j && !f32_is_nan(a[k]) ==> f32_le(a[min_index as int], a[k]),
            forall|k: int| 0 <= k < j && !f32_is_nan(a[k]) && f32_le(a[k], a[min_index as int]) && f32_le(a[min_index as int], a[k]) ==> min_index as int <= k,
        decreases a.len() - j
    {
        if a[j] == a[j] {   // not NaN
            if a[j] < a[min_index] {
                min_index = j;
                proof {
                    assert forall|k: int| 0 <= k < j && !f32_is_nan(a[k]) implies f32_le(a[min_index as int], a[k]);
                    assert forall|k: int| 0 <= k < j && !f32_is_nan(a[k]) && f32_le(a[k], a[min_index as int]) && f32_le(a[min_index as int], a[k]) implies min_index as int <= k;
                }
            } else {
                proof {
                    assert forall|k: int| 0 <= k < j && !f32_is_nan(a[k]) implies f32_le(a[min_index as int], a[k]);
                    assert forall|k: int| 0 <= k < j && !f32_is_nan(a[k]) && f32_le(a[k], a[min_index as int]) && f32_le(a[min_index as int], a[k]) implies min_index as int <= k;
                }
            }
        }
        j += 1;
    }
    min_index
}
// </vc-code>

}
fn main() {}