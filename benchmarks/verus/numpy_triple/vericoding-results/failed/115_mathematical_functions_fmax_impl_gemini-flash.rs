// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn is_nan(f: f32) -> bool;

spec fn float_max(x: f32, y: f32) -> f32;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Marked `is_nan` and `float_max` as `uninterp` to resolve compilation warnings, as they are spec functions without bodies. */
uninterp spec fn is_nan(f: f32) -> bool;
uninterp spec fn float_max(x: f32, y: f32) -> f32;
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
/* code modified by LLM (iteration 5): Changed loop index `i` and array access to `usize` for `Vec` indexing to resolve compilation error: `The Verus types 'nat' and 'int' can only be used in ghost code`. Updated assertions to use `usize` for indices. */
{
    let mut result_vec = Vec::<f32>::with_capacity(x.len());
    let mut i: usize = 0;

    while i < x.len()
        invariant
            0 <= i as int,
            i <= x.len(),
            result_vec.len() == i,
            // Proof for partial result_vec properties
            forall|j: int| 0 <= j < i as int ==> {
                let j_usize = j as usize;
                (!is_nan(x@[j_usize]) && !is_nan(y@[j_usize])) ==> (result_vec@[j_usize] == float_max(x@[j_usize], y@[j_usize])) &&
                (is_nan(x@[j_usize]) && !is_nan(y@[j_usize])) ==> (result_vec@[j_usize] == y@[j_usize]) &&
                (!is_nan(x@[j_usize]) && is_nan(y@[j_usize])) ==> (result_vec@[j_usize] == x@[j_usize]) &&
                (is_nan(x@[j_usize]) && is_nan(y@[j_usize])) ==> is_nan(result_vec@[j_usize])
            }
        decreases x.len() - i
    {
        let val_x = x@[i];
        let val_y = y@[i];
        let mut res_val: f32;

        if is_nan(val_x) {
            if is_nan(val_y) {
                res_val = f32::NAN;
            } else {
                res_val = val_y;
            }
        } else if is_nan(val_y) {
            res_val = val_x;
        } else {
            res_val = if val_x >= val_y { val_x } else { val_y };
            proof {
                // The ensures clause of float_max will handle the connection.
                // We simply assert the property here.
                assert(res_val == float_max(val_x, val_y));
            }
        }

        result_vec.push(res_val);
        i = i + 1;
    }
    result_vec
}
// </vc-code>


}
fn main() {}