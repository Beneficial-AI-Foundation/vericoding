// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn chebint(c: Vec<f32>, m: u32, k: Vec<f32>, lbnd: f32, scl: f32) -> (result: Vec<f32>)
    requires 
        m > 0,
        scl != 0.0f32,
        k.len() == m,
    ensures
        result.len() == c.len() + (m as usize),

        result.len() >= c.len(),
        m == 1 ==> result.len() == c.len() + 1,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): add invariant to satisfy vec index precondition */
{
    let mut result = c.clone();
    let mut i = 0;
    while i < m
        invariant
            i <= m,
            result.len() == c.len() + (i as usize),
            k.len() == m,
            i <= k.len(),
        decreases m - i,
    {
        result.push(k[i as usize]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}