// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): replace arithmetic operations with direct f32 operations */
fn close_float(x: f32, y: f32, rtol: f32, atol: f32, equal_nan: bool) -> (result: bool)
    ensures
        result == (
            (x == y) ||
            (equal_nan && x.is_nan() && y.is_nan()) ||
            (x.is_finite() && y.is_finite() && (
                ((x - y).abs() <= atol.max(rtol * y.abs())) ||
                ((y - x).abs() <= atol.max(rtol * x.abs()))
            ))
        ),
{
    if x == y {
        true
    } else if equal_nan && x.is_nan() && y.is_nan() {
        true
    } else if x.is_finite() && y.is_finite() {
        let diff = if x > y { x - y } else { y - x };
        let tol1 = if atol > rtol * y.abs() { atol } else { rtol * y.abs() };
        let tol2 = if atol > rtol * x.abs() { atol } else { rtol * x.abs() };
        diff <= tol1 || diff <= tol2
    } else {
        false
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
/* code modified by LLM (iteration 5): fixed indexing syntax */
{
    let len = a.len();
    let mut result = Vec::new();
    let mut i = 0;
    while i < len
        invariant
            i <= len,
            result@.len() == i,
            forall|j: int| 0 <= j && j < i ==> result@[j] == close_float(a@[j], b@[j], rtol, atol, equal_nan)
    {
        let close = close_float(a@[i], b@[i], rtol, atol, equal_nan);
        result.push(close);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}