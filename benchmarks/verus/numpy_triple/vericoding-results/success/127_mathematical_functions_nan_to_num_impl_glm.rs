// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn convert_nan(x: f64) -> f64 {
    if x != x {
        0.0
    } else {
        x
    }
}
// </vc-helpers>

// <vc-spec>
fn nan_to_num(x: Vec<f64>) -> (result: Vec<f64>)
    ensures 
        result.len() == x.len(),
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    for i in 0..x.len()
        invariant 
            result.len() == i
    {
        result.push(convert_nan(x[i]));
    }
    result
}
// </vc-code>

}
fn main() {}