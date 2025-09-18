// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn f32_is_nan(x: f32) -> bool;
spec fn f32_le(a: f32, b: f32) -> bool;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed duplicate definitions and kept only the uninterp ones. */
uninterp spec fn f32_is_nan(x: f32) -> bool;
uninterp spec fn f32_le(a: f32, b: f32) -> bool;
spec fn f32_le_strict(a_val: f32, b_val: f32) -> bool { f32_le(a_val, b_val) && !f32_le(b_val, a_val) }
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
/* code modified by LLM (iteration 5): Fixed loop termination conditions and refined invariants for correctness */
{
    let mut min_idx: usize = 0;
    let mut i: usize = 0;

    while a.len() > 0 && i < a.len()
        invariant 
            0 <= min_idx < a.len(),
            i <= a.len(),
            !f32_is_nan(a[min_idx]),
            forall|k: int| 0 <= k < i && !f32_is_nan(a[k]) ==> f32_le(a[min_idx], a[k]),
            forall|k: int| 
                0 <= k < i && 
                !f32_is_nan(a[k]) && 
                f32_le(a[k], a[min_idx]) && 
                f32_le(a[min_idx], a[k]) 
            ==> 
                min_idx as int <= k,
    {
        if !f32_is_nan(a[i]) {
            if f32_is_nan(a[min_idx]) || f32_le_strict(a[i], a[min_idx]) {
                min_idx = i;
            }
        }
        i = i + 1;
    }
    min_idx
}
// </vc-code>

}
fn main() {}