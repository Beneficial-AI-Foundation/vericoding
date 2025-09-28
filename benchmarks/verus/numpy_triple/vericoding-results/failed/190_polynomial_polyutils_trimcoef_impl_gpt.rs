// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): absolute value for f32 */
fn abs_f32(x: f32) -> (r: f32) {
    if x < 0.0f32 { -x } else { x }
}

/* helper modified by LLM (iteration 5): check if magnitude exceeds tolerance */
fn is_significant(x: f32, tol: f32) -> (b: bool) {
    abs_f32(x) > tol
}
// </vc-helpers>

// <vc-spec>
fn trimcoef(c: Vec<f32>, tol: f32) -> (result: Vec<f32>)
    ensures
        result.len() >= 1,
        result.len() <= c.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): avoid mutating the input vector; handle empty input conservatively, find last significant coefficient, and copy the required prefix */
    let n: usize = c.len();
    if n == 0usize {
        // No elements to trim; conservative return
        return Vec::new();
    }

    let mut last_idx: usize = 0usize;
    let mut found: bool = false;
    let mut i: usize = 0usize;

    while i < n
        invariant
            i <= n,
            n == c.len(),
            last_idx < n || !found,
        decreases (n as int) - (i as int)
    {
        let val = c[i];
        if abs_f32(val) > tol {
            last_idx = i;
            found = true;
        }
        i = i + 1usize;
    }

    let end_idx: usize = if found { last_idx + 1usize } else { 1usize };
    let mut res: Vec<f32> = Vec::new();
    let mut j: usize = 0usize;
    while j < end_idx
        invariant
            j <= end_idx,
            end_idx <= n,
            res.len() == j,
        decreases (end_idx as int) - (j as int)
    {
        res.push(c[j]);
        j = j + 1usize;
    }

    res
}
// </vc-code>

}
fn main() {}