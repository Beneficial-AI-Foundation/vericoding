// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes */
spec fn is_close_to_zero(x: f32, tol: f32) -> bool { x.abs() <= tol }
// </vc-helpers>

// <vc-spec>
fn trimcoef(c: Vec<f32>, tol: f32) -> (result: Vec<f32>)
    ensures
        result.len() >= 1,
        result.len() <= c.len(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Add assertion to handle `c.len() == 0` case explicitly and cast to `usize` for `c.index` within `is_close_to_zero` call. */
{
    if c.len() == 0 {
        let mut r = Vec::new();
        r.push(0.0f32);
        return r;
    }

    let mut k: usize = c.len() - 1;
    while k >= 0
        invariant 
            k < c.len(),
            forall|j: int| (k as int) < j && j < (c.len() as int) ==> is_close_to_zero(c.index(j as nat), tol),
            c.len() >= 1,
        decreases k
    {
        if !(is_close_to_zero(c.index(k as usize), tol)) {
            break;
        }
        if k == 0 { break; } // Avoid underflow by explicitly breaking when k would become negative
        k = k - 1;
    }

    let mut result_vec = Vec::new();
    let mut i: usize = 0;
    while i <= k
        invariant
            i <= k + 1,
            (result_vec.len() as usize) == i,
            k < c.len(),
            i <= c.len(),
        decreases (k + 1) - i
    {
        result_vec.push(c.index(i));
        i = i + 1;
    }

    if result_vec.len() == 0 {
        result_vec.push(0.0f32);
    }

    result_vec
}
// </vc-code>

}
fn main() {}