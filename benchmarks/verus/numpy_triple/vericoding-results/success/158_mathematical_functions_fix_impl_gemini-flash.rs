// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): no changes needed */
fn min(a: f64, b: f64) -> f64 {
    if a < b { a } else { b }
}

fn max(a: f64, b: f64) -> f64 {
    if a > b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn numpy_fix(x: Vec<f64>) -> (result: Vec<f64>)
    ensures result.len() == x.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): add decreases clause to while loop */
{
    let mut result = Vec::with_capacity(x.len());
    let mut i = 0;
    while i < x.len()
        invariant
            result.len() == i,
            result.len() <= x.len(),
            i <= x.len(),
        decreases x.len() - i
    {
        let val = x[i];
        let fixed_val = min(max(val, 0.0), 255.0);
        result.push(fixed_val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}