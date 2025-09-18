// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn legmulx(c: Vec<f32>) -> (result: Vec<f32>)
    requires c.len() > 0,
    ensures
        result.len() == c.len() + 1,
        result[0] == 0.0f32,
        result[1] == c[0],
        true, // Polynomial coefficients exist (simplified)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): replaced Vec::with_capacity with Vec::new to avoid immediate overflow error */
    let n = c.len();
    let mut result = Vec::new();
    result.push(0.0f32);

    let mut i: usize = 0;
    while i < n
        invariant
            n == c.len(),
            i <= n,
            result.len() == i + 1,
            result@.len() == i + 1,
            result@[0] == 0.0f32,
            forall|j: int| 1 <= j < result@.len() ==> result@[j] == c@[(j - 1) as int],
        decreases n - i
    {
        result.push(c[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}