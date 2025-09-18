// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed unused helper to avoid trigger errors */

// </vc-helpers>

// <vc-spec>
fn diagflat(v: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == v.len() * v.len(),
        forall|i: int| 0 <= i < v.len() ==> #[trigger] result[i * v.len() + i] == v[i],
        forall|i: int, j: int| 0 <= i < v.len() && 0 <= j < v.len() && i != j ==> #[trigger] result[i * v.len() + j] == 0.0f32
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Separated quantifiers in invariant to add triggers */
{
    let n = v.len();
    let mut result = Vec::new();
    while result.len() < n * n
        invariant
            result@.len() <= (n as int) * (n as int),
            forall|k: int| 0 <= k < result@.len() && ((k / (n as int)) == (k % (n as int))) ==> #[trigger] result@[k] == v@[(k / (n as int))],
            forall|k: int| 0 <= k < result@.len() && ((k / (n as int)) != (k % (n as int))) ==> #[trigger] result@[k] == 0.0f32
        decreases ((n as int) * (n as int)) - (result.len() as int)
    {
        result.push(if result.len() % n == 0 {
            v[result.len() / n]
        } else {
            0.0f32
        });
    }
    result
}
// </vc-code>

}
fn main() {}