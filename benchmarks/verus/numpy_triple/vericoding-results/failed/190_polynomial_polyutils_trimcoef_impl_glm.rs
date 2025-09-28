// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed nat usage by changing to int for executable code */
fn trimcoef_helper(c: Vec<f32>, tol: f32, start: int, end: int) -> (result: Vec<f32>)
    requires
        0 <= start <= end,
        end <= c.len(),
    ensures
        result.len() >= 0,
        result.len() <= end - start,
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result@[i] == c@[start + i]
{
    if start == end {
        Vec::new()
    } else if c@[start].abs() > tol {
        let mut res = Vec::new();
        res.push(c@[start]);
        res
    } else {
        trimcoef_helper(c, tol, start + 1, end)
    }
}
// </vc-helpers>

// <vc-spec>
fn trimcoef(c: Vec<f32>, tol: f32) -> (result: Vec<f32>)
    ensures
        result.len() >= 1,
        result.len() <= c.len(),
// </vc-spec>
// <vc-code>
{ /* code modified by LLM (iteration 5): changed nat to int for executable variables */
    if c.len() == 0 {
        vec![0.0f32]
    } else {
        let mut i = 0;
        while i < c.len() && c@[i].abs() <= tol
            invariant
                0 <= i <= c.len(),
            decreases (c.len() - i) as int
        {
            i += 1;
        }
        
        if i == c.len() {
            vec![0.0f32]
        } else {
            let mut result = Vec::new();
            let mut j = i;
            while j < c.len()
                invariant
                    i <= j <= c.len(),
                    result.len() == j - i,
                    forall|k: int| 0 <= k < result.len() ==> #[trigger] result@[k] == c@[i + k],
                decreases (c.len() - j) as int
            {
                result.push(c@[j]);
                j += 1;
            }
            result
        }
    }
}
// </vc-code>

}
fn main() {}