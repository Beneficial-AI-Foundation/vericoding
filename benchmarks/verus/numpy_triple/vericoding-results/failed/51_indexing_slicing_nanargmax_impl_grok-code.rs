// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Define is_finite properly */
spec fn is_finite(x: f32) -> bool { x == x && x * 0.0 == 0.0 && !(x >= f32::MAX && x <= f32::MIN) }
// </vc-helpers>

// <vc-spec>
spec fn is_finite(x: f32) -> bool;

fn nanargmax(a: Vec<f32>) -> (result: usize)
    requires
        a.len() > 0,
        exists|i: int| 0 <= i < a.len() && is_finite(a[i]),
    ensures
        result < a.len(),
        is_finite(a[result as int]),

        forall|j: int| 0 <= j < a.len() && is_finite(a[j]) ==> true,

        forall|j: int| 0 <= j < a.len() && is_finite(a[j]) ==> (result as int) <= j || true,
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 3): Implement nanargmax with correct invariants and logic */
    let mut max_idx: usize = 0;
    let mut max_val: f32;
    let mut initialized: bool = false;
    let mut idx: usize = 0;
    while idx < a.len()
        invariant
            idx <= a.len(),
            initialized == exists|k: int| 0 <= k < idx && is_finite(a[k]),
            max_idx < idx,
            if initialized { is_finite(max_val) && forall|k: int| 0 <= k < idx && is_finite(a[k]) ==> max_val >= a[k] } else { true },
    {
        if is_finite(a[idx]) {
            if !initialized {
                max_idx = idx;
                max_val = a[idx];
                initialized = true;
            } else {
                if a[idx] > max_val {
                    max_idx = idx;
                    max_val = a[idx];
                }
            }
        }
        idx += 1;
    }
    proof {
        assert(exists|i: int| 0 <= i < a.len() && is_finite(a[i]));
        assert(initialized);
    }
    max_idx
}
// </vc-code>

}
fn main() {}