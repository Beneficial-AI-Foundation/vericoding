// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn id(x: int) -> int { x }

proof fn lemma_add_zero(x: int)
    ensures x + 0 == x
{ }
// </vc-helpers>

// <vc-spec>
fn vstack(a: Vec<f32>, b: Vec<f32>) -> (result: Vec<Vec<f32>>)
    requires a.len() == b.len(),
    ensures
        result.len() == 2,
        result[0].len() == a.len(),
        result[1].len() == b.len(),
        forall|j: int| 0 <= j < a.len() ==> result[0][j] == a[j],
        forall|j: int| 0 <= j < b.len() ==> result[1][j] == b[j]
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<Vec<f32>> = Vec::new();
    result.push(a);
    result.push(b);
    result
}
// </vc-code>

}
fn main() {}