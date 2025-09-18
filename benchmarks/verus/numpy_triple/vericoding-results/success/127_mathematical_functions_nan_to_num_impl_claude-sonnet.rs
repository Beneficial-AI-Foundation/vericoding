// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn nan_to_num(x: Vec<f64>) -> (result: Vec<f64>)
    ensures 
        result.len() == x.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): removed is_nan() call which is not supported in Verus, using direct comparison instead */
    let mut result = Vec::new();
    for i in 0..x.len()
        invariant
            result.len() == i
    {
        let val = x[i];
        if val != val {
            result.push(0.0);
        } else {
            result.push(val);
        }
    }
    result
}
// </vc-code>

}
fn main() {}