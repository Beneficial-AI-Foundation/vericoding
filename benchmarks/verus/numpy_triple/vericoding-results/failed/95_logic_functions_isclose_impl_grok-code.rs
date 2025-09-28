// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn are_close(a: f32, b: f32, rtol: f32, atol: f32, equal_nan: bool) -> bool {
    if equal_nan && a.is_nan() && b.is_nan() {
        true
    } else if !(a.is_finite() && b.is_finite()) {
        false
    } else {
        let diff = (a - b).abs();
        let tol = atol + rtol * b.abs();
        diff <= tol
    }
}
// </vc-helpers>

// <vc-spec>
fn isclose(a: Vec<f32>, b: Vec<f32>, rtol: f32, atol: f32, equal_nan: bool) -> (result: Vec<bool>)
    requires 
        a@.len() == b@.len(),
    ensures
        result@.len() == a@.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): cast length to int for proper range and indexing */
    let len: int = a@.len() as int;
    let mut result: Vec<bool> = Vec::new();
    for i in 0..len
        invariant
            result@.len() == i,
    {
        let close = are_close(a@[i], b@[i], rtol, atol, equal_nan);
        result.push(close);
    }
    result
}
// </vc-code>


}
fn main() {}