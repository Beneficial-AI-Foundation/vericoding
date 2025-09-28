// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): float NaN detection */
fn f32_is_nan(x: f32) -> bool {
    x != x
}

/* helper modified by LLM (iteration 5): absolute value for f32 */
fn f32_abs(x: f32) -> f32 {
    if x < 0.0 { -x } else { x }
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
    /* code modified by LLM (iteration 5): implement isclose using runtime indices and helpers */
    let n: usize = a.len();
    let mut res: Vec<bool> = Vec::new();
    while res.len() < n
        invariant
            res@.len() == res.len(),
            res@.len() <= a@.len(),
        decreases a@.len() - res@.len()
    {
        let idx: usize = res.len();
        let ai: f32 = a[idx];
        let bi: f32 = b[idx];
        let eq: bool =
            if ai == bi {
                true
            } else if f32_is_nan(ai) && f32_is_nan(bi) && equal_nan {
                true
            } else {
                let diff: f32 = f32_abs(ai - bi);
                let tol: f32 = atol + rtol * f32_abs(bi);
                diff <= tol
            };
        res.push(eq);
    }
    res
}
// </vc-code>


}
fn main() {}