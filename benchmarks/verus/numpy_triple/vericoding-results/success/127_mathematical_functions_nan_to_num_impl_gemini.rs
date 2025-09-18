// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): changed function from proof to exec to fix compilation error */
fn is_f64_nan(f: f64) -> bool {
    f != f
}
// </vc-helpers>

// <vc-spec>
fn nan_to_num(x: Vec<f64>) -> (result: Vec<f64>)
    ensures 
        result.len() == x.len(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): no change to logic, fix was in helper function mode */
{
    let mut result: Vec<f64> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
        decreases x.len() - i
    {
        let val = x[i];
        if is_f64_nan(val) {
            result.push(0.0);
        } else {
            result.push(val);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}