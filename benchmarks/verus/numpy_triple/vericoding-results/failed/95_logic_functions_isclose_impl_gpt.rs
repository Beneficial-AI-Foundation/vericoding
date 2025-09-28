// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simple NaN predicate for f32 */
fn is_nan_f32(x: f32) -> bool {
    x.is_nan()
}

/* helper modified by LLM (iteration 5): absolute value now names return value to allow ensures about result */
fn abs_f32(x: f32) -> (result: f32)
    requires
        !x.is_nan(),
    ensures
        result >= 0.0f32,
{
    if x < 0.0f32 { -x } else { x }
}

/* helper modified by LLM (iteration 5): guarded isclose computation to avoid NaN/infinite arithmetic */
fn isclose_elem(a: f32, b: f32, rtol: f32, atol: f32, equal_nan: bool) -> bool {
    if is_nan_f32(a) || is_nan_f32(b) {
        equal_nan && is_nan_f32(a) && is_nan_f32(b)
    } else if a == b {
        true
    } else if a.is_infinite() || b.is_infinite() {
        false
    } else if is_nan_f32(rtol) || is_nan_f32(atol) || rtol.is_infinite() || atol.is_infinite() {
        false
    } else {
        let diff = abs_f32(a - b);
        let tol = atol + rtol * abs_f32(b);
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
    /* code modified by LLM (iteration 5): iterate element-wise, using guarded isclose computation */
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < a.len() && i < b.len()
        invariant
            result@.len() == i as int,
            i <= a.len(),
            i <= b.len(),
            a@.len() == b@.len(),
        decreases (a.len() - i) as int
    {
        let v = isclose_elem(a[i], b[i], rtol, atol, equal_nan);
        result.push(v);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}