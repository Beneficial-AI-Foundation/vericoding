// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn trimcoef(c: Vec<f32>, tol: f32) -> (result: Vec<f32>)
    ensures
        result.len() >= 1,
        result.len() <= c.len(),
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i = c.len();
    while i > 0
        invariant
            i <= c.len(),
        decreases i,
    {
        i -= 1;
        if c[i] > tol || c[i] < -tol {
            break;
        }
    }
    if i == 0 && c.len() > 0 && !(c[0] > tol || c[0] < -tol) {
        i = 1;
    } else {
        i += 1;
    }
    let mut j = 0;
    while j < i
        invariant
            j <= i,
            result.len() == j,
            i >= 1,
            i <= c.len(),
        decreases i - j,
    {
        result.push(c[j]);
        j += 1;
    }
    result
}
// </vc-code>

}
fn main() {}