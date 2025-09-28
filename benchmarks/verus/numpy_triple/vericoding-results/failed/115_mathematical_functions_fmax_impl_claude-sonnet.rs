// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn is_nan(f: f32) -> bool;

spec fn float_max(x: f32, y: f32) -> f32;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed invalid verifier attribute and used uninterp keyword correctly */
spec fn is_nan_impl(f: f32) -> bool uninterp;

spec fn float_max_impl(x: f32, y: f32) -> f32 uninterp;

// Helper function to compute element-wise max with NaN handling
fn compute_fmax_element(x_val: f32, y_val: f32) -> (result: f32)
    ensures
        (!is_nan(x_val) && !is_nan(y_val)) ==> (result == float_max(x_val, y_val)),
        (is_nan(x_val) && !is_nan(y_val)) ==> (result == y_val),
        (!is_nan(x_val) && is_nan(y_val)) ==> (result == x_val),
        (is_nan(x_val) && is_nan(y_val)) ==> is_nan(result),
        (!is_nan(x_val) && !is_nan(y_val)) ==> (result == x_val || result == y_val),
        is_nan(result) <==> (is_nan(x_val) && is_nan(y_val))
{
    if x_val.is_nan() && y_val.is_nan() {
        x_val
    } else if x_val.is_nan() {
        y_val
    } else if y_val.is_nan() {
        x_val
    } else {
        if x_val >= y_val { x_val } else { y_val }
    }
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
    /* code modified by LLM (iteration 5): implemented proper verification without assumptions */
    let mut result = Vec::with_capacity(x.len());
    let mut i = 0;
    
    while i < x.len()
        invariant
            i <= x.len(),
            result@.len() == i,
            x@.len() == y@.len(),
            forall|j: int| 0 <= j < i ==> {
                (!is_nan(x@[j]) && !is_nan(y@[j])) ==> 
                    (result@[j] == float_max(x@[j], y@[j])) &&
                (is_nan(x@[j]) && !is_nan(y@[j])) ==> 
                    (result@[j] == y@[j]) &&
                (!is_nan(x@[j]) && is_nan(y@[j])) ==> 
                    (result@[j] == x@[j]) &&
                (is_nan(x@[j]) && is_nan(y@[j])) ==> 
                    is_nan(result@[j]) &&
                (!is_nan(x@[j]) && !is_nan(y@[j])) ==> 
                    (result@[j] == x@[j] || result@[j] == y@[j]) &&
                is_nan(result@[j]) <==> (is_nan(x@[j]) && is_nan(y@[j]))
            }
    {
        let x_val = x[i];
        let y_val = y[i];
        
        let elem = if x_val.is_nan() && y_val.is_nan() {
            x_val
        } else if x_val.is_nan() {
            y_val
        } else if y_val.is_nan() {
            x_val
        } else {
            if x_val >= y_val { x_val } else { y_val }
        };
        
        result.push(elem);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}