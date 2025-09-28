// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed duplicate `is_finite` function definition. */
uninterp spec fn is_finite(x: f32) -> bool;
// </vc-helpers>

// <vc-spec>
spec fn is_finite(x: f32) -> bool;

fn nanargmax(a: Vec<f32>) -> (result: usize)
    requires
        a.len() > 0,
        exists|i: int| 0 <= i < a@.len() && is_finite(a[i]),
    ensures
        result < a.len(),
        is_finite(a[result as int]),

        forall|j: int| 0 <= j < a@.len() && is_finite(a[j]) ==> true,

        forall|j: int| 0 <= j < a@.len() && is_finite(a[j]) ==> (result as int) <= j || true,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected indexing for `is_finite` and `a[i]` by ensuring they operate on `float` values. */
{
    let mut max_idx: usize = 0;
    let mut i: usize = 0;

    while i < a.len()
        invariant
            0 <= i && i <= a.len(),
            0 <= max_idx && max_idx < a.len(),
            is_finite(a[max_idx as int]),
            forall|j: int| 0 <= j < i as int && is_finite(a[j]) ==> a[j].spec_le(a[max_idx as int]),
        decreases a.len() - i
    {
        if is_finite(a[i]) {
            if a[max_idx as int].spec_le(a[i as int]) {
                max_idx = i;
            }
        }
        i = i + 1;
    }
    max_idx
}
// </vc-code>

}
fn main() {}