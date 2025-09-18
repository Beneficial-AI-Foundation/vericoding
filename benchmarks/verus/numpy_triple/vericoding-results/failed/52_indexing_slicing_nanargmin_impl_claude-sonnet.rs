// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn f32_is_nan(x: f32) -> bool;
spec fn f32_le(a: f32, b: f32) -> bool;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed duplicate declarations and marked uninterpreted functions properly */
spec fn has_non_nan(a: Vec<f32>) -> bool {
    exists|i: int| 0 <= i < a.len() && !f32_is_nan(a[i])
}

spec fn is_min_among_non_nan(a: Vec<f32>, idx: int) -> bool {
    0 <= idx < a.len() &&
    !f32_is_nan(a[idx]) &&
    forall|j: int| 0 <= j < a.len() && !f32_is_nan(a[j]) ==> f32_le(a[idx], a[j])
}

spec fn is_leftmost_min(a: Vec<f32>, idx: int) -> bool {
    is_min_among_non_nan(a, idx) &&
    forall|j: int| 0 <= j < a.len() && !f32_is_nan(a[j]) && f32_le(a[j], a[idx]) && f32_le(a[idx], a[j]) ==> idx <= j
}
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
    /* code modified by LLM (iteration 5): proper implementation checking for NaN and finding minimum */
    let mut result = 0;
    let mut found_valid = false;
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result < a.len(),
            exists|k: int| 0 <= k < a.len() && !f32_is_nan(a[k]),
            if found_valid {
                !f32_is_nan(a[result as int]) &&
                forall|j: int| 0 <= j < i && !f32_is_nan(a[j]) ==> f32_le(a[result as int], a[j]) &&
                forall|j: int| 0 <= j < i && !f32_is_nan(a[j]) && f32_le(a[j], a[result as int]) && f32_le(a[result as int], a[j]) ==> result as int <= j
            } else {
                forall|j: int| 0 <= j < i ==> f32_is_nan(a[j])
            }
    {
        if !found_valid {
            if !f32_is_nan(a[i]) {
                result = i;
                found_valid = true;
            }
        } else {
            if !f32_is_nan(a[i]) && f32_le(a[i], a[result as int]) {
                result = i;
            }
        }
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}