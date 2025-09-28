// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn f32_is_nan(x: f32) -> bool;
spec fn f32_le(a: f32, b: f32) -> bool;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added uninterp markers to spec functions to fix compilation warnings */
#[verifier(uninterp)]
spec fn f32_is_nan(x: f32) -> bool;
#[verifier(uninterp)]
spec fn f32_le(a: f32, b: f32) -> bool;

spec fn should_update(curr_val: f32, curr_idx: int, cand_val: f32, cand_idx: int) -> bool {
    f32_le(cand_val, curr_val) && !f32_le(curr_val, cand_val) ||
    (f32_le(cand_val, curr_val) && f32_le(curr_val, cand_val) && cand_idx < curr_idx)
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
/* code modified by LLM (iteration 2): fixed type errors by using ghost variables in conditions and loops, corrected invariant formatting with separate forall clauses */
{
    let mut min_idx: usize = 0;
    while min_idx < a.len()
        invariant
            min_idx <= a.len(),
        decreases (a.len() as int - min_idx)
    {
        let ghost curr = a@[min_idx as int];
        if !f32_is_nan(curr) {
            break;
        }
        min_idx += 1;
    }
    let mut i: usize = min_idx + 1;
    while i < a.len()
        invariant
            min_idx < a.len(),
            !f32_is_nan(a@[min_idx as int]),
            i > min_idx,
            forall |k: int| 0 <= k < i && !f32_is_nan(a@[k as int]) ==> f32_le(a@[min_idx as int], a@[k as int]),
            forall |k: int| 0 <= k < i && !f32_is_nan(a@[k as int]) && f32_le(a@[k as int], a@[min_idx as int]) && f32_le(a@[min_idx as int], a@[k as int]) ==> k >= min_idx as int,
        decreases (a.len() as int - i)
    {
        let ghost cand_val = a@[i as int];
        if !f32_is_nan(cand_val) {
            if should_update(a@[min_idx as int], min_idx as int, cand_val, i as int) {
                min_idx = i;
            }
        }
        i += 1;
    }
    min_idx
}
// </vc-code>

}
fn main() {}