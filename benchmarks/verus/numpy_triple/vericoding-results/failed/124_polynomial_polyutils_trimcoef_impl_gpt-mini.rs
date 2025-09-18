// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fabs: absolute value for f32 */
fn fabs(x: f32) -> f32 { if x >= 0.0 { x } else { -x } }

/* helper modified by LLM (iteration 5): max_usize: return max of two usize values */
spec fn max_usize(a: usize, b: usize) -> usize { if a >= b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn trimcoef(c: Vec<f32>, tol: f32) -> (result: Vec<f32>)
    ensures
        result.len() >= 1,
        result.len() <= c.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use usize indices and fabs helper; find last non-tol coefficient and build result */

    let mut last_plus1: usize = 0usize;
    let mut k: usize = c.len();
    while k > 0
        invariant k <= c.len() && last_plus1 <= c.len()
        decreases k
    {
        let idx: usize = k - 1;
        if fabs(c[idx]) > tol {
            last_plus1 = k;
            k = 0usize;
        } else {
            k = idx;
        }
    }

    let cut: usize = if last_plus1 == 0usize { 1usize } else { last_plus1 };

    let mut result = Vec::<f32>::new();
    let mut j: usize = 0usize;
    while j < cut
        invariant j <= cut && result.len() == j
        decreases cut - j
    {
        result.push(c[j]);
        j = j + 1usize;
    }

    result
}
// </vc-code>

}
fn main() {}