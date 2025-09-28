// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn f32_is_nan(x: f32) -> bool;
spec fn f32_le(a: f32, b: f32) -> bool;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): marked spec functions as uninterp to fix compilation errors */
spec fn f32_is_nan(x: f32) -> bool
    uninterp;

spec fn f32_le(a: f32, b: f32) -> bool
    uninterp;
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
{
    /* code modified by LLM (iteration 5): fixed compilation error by removing duplicate spec function calls */
    let mut min_idx: usize = 0;
    let mut found_valid = false;
    
    // Find first non-NaN element
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            !found_valid ==> forall|k: int| 0 <= k < i ==> f32_is_nan(a[k]),
            found_valid ==> min_idx < a.len() && !f32_is_nan(a[min_idx as int]),
    {
        if !f32_is_nan(a[i]) {
            min_idx = i;
            found_valid = true;
            break;
        }
        i += 1;
    }
    
    // Find minimum among remaining elements
    let mut j = min_idx + 1;
    while j < a.len()
        invariant
            min_idx < a.len(),
            !f32_is_nan(a[min_idx as int]),
            min_idx + 1 <= j <= a.len(),
            forall|k: int| 0 <= k < j && !f32_is_nan(a[k]) ==> f32_le(a[min_idx as int], a[k]),
            forall|k: int| 0 <= k < j && !f32_is_nan(a[k]) && f32_le(a[k], a[min_idx as int]) && f32_le(a[min_idx as int], a[k]) ==> min_idx as int <= k,
    {
        if !f32_is_nan(a[j]) {
            if f32_le(a[j], a[min_idx]) {
                min_idx = j;
            }
        }
        j += 1;
    }
    
    min_idx
}
// </vc-code>

}
fn main() {}