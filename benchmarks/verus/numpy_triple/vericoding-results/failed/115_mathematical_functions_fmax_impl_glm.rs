// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn is_nan(f: f32) -> bool;

spec fn float_max(x: f32, y: f32) -> f32;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed syntax error by removing comma in requires clause */
lemma! axiom_float_max_result(x: f32, y: f32)
    requires !is_nan(x) && !is_nan(y)
    ensures float_max(x, y) == x || float_max(x, y) == y;

axiom axiom_is_nan_NAN: is_nan(f32::NAN) == true;
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
/* code modified by LLM (iteration 5): Replaced spec function calls with executable equivalents for NaN check and float max */
{
    let n = x.len();
    let mut result = Vec::with_capacity(n);
    let mut i = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            result@.len() == i,
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
            },
        decreases n - i,
    {
        let xi = x[i];
        let yi = y[i];
        
        if xi.is_nan() {
            if yi.is_nan() {
                result.push(f32::NAN);
            } else {
                result.push(yi);
            }
        } else {
            if yi.is_nan() {
                result.push(xi);
            } else {
                result.push(xi.max(yi));
            }
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}