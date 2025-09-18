// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn f32_is_nan(x: f32) -> bool;
spec fn f32_le(a: f32, b: f32) -> bool;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): convenience predicates for NaN checks and min on f32 values */
spec fn is_not_nan(x: f32) -> bool { !f32_is_nan(x) }
spec fn min_f32(a: f32, b: f32) -> f32 { if f32_is_nan(a) { b } else if f32_is_nan(b) { a } else if f32_le(a, b) { a } else { b } }
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
    /* code modified by LLM (iteration 5): find first non-NaN index then scan for min, using invariants in loop headers */
    let n = a.len();
    let mut k: usize = 0;
    while k < n && f32_is_nan(a[k as int])
        invariant k <= n;
        invariant exists|p: int| (k as int) <= p && p < (n as int) && !f32_is_nan(a[p]);
        decreases n - k;
    {
        k = k + 1;
    }
    proof {
        // loop exited, so not (k < n && f32_is_nan(a[k]))
        assert(!(k < n && f32_is_nan(a[k as int])));
        // from invariant there is some non-NaN at or after k and before n, so k < n
        assert(exists|p: int| (k as int) <= p && p < (n as int) && !f32_is_nan(a[p]));
        assert(k < n);
        assert(!f32_is_nan(a[k as int]));
    }
    let mut min_idx: usize = k;
    let mut i: usize = k + 1;
    while i < n
        invariant k <= n;
        invariant min_idx < n;
        invariant !f32_is_nan(a[min_idx as int]);
        invariant forall|j: int| (k as int) <= j && j < (i as int) && !f32_is_nan(a[j]) ==> f32_le(a[min_idx as int], a[j]);
        decreases n - i;
    {
        if !f32_is_nan(a[i as int]) && f32_le(a[i as int], a[min_idx as int]) {
            min_idx = i;
        }
        i = i + 1;
    }
    min_idx
}
// </vc-code>

}
fn main() {}