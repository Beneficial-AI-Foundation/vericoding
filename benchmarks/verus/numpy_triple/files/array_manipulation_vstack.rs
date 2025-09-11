// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}