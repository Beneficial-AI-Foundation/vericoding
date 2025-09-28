// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): define is_nan using self-comparison */
fn is_nan(x: f64) -> bool {
    x != x
}
// </vc-helpers>

// <vc-spec>
fn nan_to_num(x: Vec<f64>) -> (result: Vec<f64>)
    ensures 
        result.len() == x.len(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): use helper function for NaN check */
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
        decreases x.len() - i
    {
        let val = x[i];
        if is_nan(val) {
            result.push(0.0);
        } else {
            result.push(val);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}