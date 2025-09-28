// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn abs_f32(x: f32) -> f32 {
    if x < 0.0 {
        -x
    } else {
        x
    }
}
// </vc-helpers>

// <vc-spec>
fn fabs(x: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == x.len()
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            result.len() == i,
            i <= x.len(),
        decreases x.len() - i
    {
        let abs_val = abs_f32(x[i]);
        result.push(abs_val);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}