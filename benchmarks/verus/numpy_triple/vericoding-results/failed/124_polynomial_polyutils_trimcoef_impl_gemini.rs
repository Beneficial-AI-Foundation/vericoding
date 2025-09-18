// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn f32_abs(x: f32) -> f32 { if x < 0.0 { -x } else { x } }
// </vc-helpers>

// <vc-spec>
fn trimcoef(c: Vec<f32>, tol: f32) -> (result: Vec<f32>)
    ensures
        result.len() >= 1,
        result.len() <= c.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed type error and added missing decreases clauses */
    let mut new_len = c.len();
    while new_len > 1 && f32_abs(c[new_len - 1]) <= tol
        invariant
            1 <= new_len <= c.len(),
        decreases new_len
    {
        new_len = new_len - 1;
    }

    let mut result = Vec::with_capacity(new_len);
    let mut i: usize = 0;
    while i < new_len
        invariant
            0 <= i <= new_len,
            result.len() == i,
            1 <= new_len <= c.len(),
            result.view() == c.view().subrange(0, i as int),
        decreases new_len - i
    {
        result.push(c[i]);
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}