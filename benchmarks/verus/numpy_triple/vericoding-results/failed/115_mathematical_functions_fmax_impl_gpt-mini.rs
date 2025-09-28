// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn is_nan(f: f32) -> bool;

spec fn float_max(x: f32, y: f32) -> f32;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): trivial helper to satisfy placeholder */
proof fn helpers_trivial()
    ensures
        true,
{
}

// </vc-helpers>

// <vc-spec>
fn fmax(x: Vec<f32>, y: Vec<f32>) -> (result: Vec<f32>)
    requires x@.len() == y@.len(),
    ensures 
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < result@.len() ==> {
            /* Core NaN handling behavior */
            (!is_nan(x@[i]) && !is_nan(y@[i])) ==> 
                (result@[i] == float_max(x@[i], y@[i])) &&
            (is_nan(x@[i]) && !is_nan(y@[i])) ==> 
                (result@[i] == y@[i]) &&
            (!is_nan(x@[i]) && is_nan(y@[i])) ==> 
                (result@[i] == x@[i]) &&
            (is_nan(x@[i]) && is_nan(y@[i])) ==> 
                is_nan(result@[i]) &&
            /* Mathematical properties for non-NaN cases */
            (!is_nan(x@[i]) && !is_nan(y@[i])) ==> 
                (result@[i] == x@[i] || result@[i] == y@[i]) &&
            /* NaN preservation: result is NaN iff both inputs are NaN */
            is_nan(result@[i]) <==> (is_nan(x@[i]) && is_nan(y@[i]))
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): implement element-wise fmax using usize indices and proper invariants */
    let n: usize = x.len();
    let mut i: usize = 0;
    let mut result_mut: Vec<f32> = Vec::new();
    while i < n
        invariant
            result_mut@.len() == i as nat,
        decreases (n - i) as nat
    {
        let xv: f32 = x[i];
        let yv: f32 = y[i];
        if is_nan(xv) {
            if is_nan(yv) {
                // both NaN: preserve a NaN value (take xv)
                result_mut.push(xv);
            } else {
                // x is NaN, y is not
                result_mut.push(yv);
            }
        } else {
            if is_nan(yv) {
                // y is NaN, x is not
                result_mut.push(xv);
            } else {
                // both not NaN: use float_max
                result_mut.push(float_max(xv, yv));
            }
        }
        i = i + 1;
    }
    result_mut
}

// </vc-code>


}
fn main() {}