// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn legmulx(c: Vec<f32>) -> (result: Vec<f32>)
    requires c@.len() > 0,
    ensures
        result@.len() == c@.len() + 1,
        result[0] == 0.0f32,
        result[1] == c[0],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed type mismatch by using 0.0f32 for f32 values */
{
    let mut result: Vec<f32> = Vec::new();
    result.push(0.0f32);
    let mut i = 0;
    while i < c.len()
        invariant
            0 <= i <= c.len(),
            result.len() == i + 1,
            result[0] == 0.0f32,
            forall|j: int| 0 < j <= i ==> #[trigger] result[j as int] == c[(j - 1) as int],
            result@.len() == i + 1,
        decreases c@.len() - i,
    {
        result.push(c[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}