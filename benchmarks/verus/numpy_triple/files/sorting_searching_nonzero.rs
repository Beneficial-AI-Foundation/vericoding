// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn nonzero(a: Vec<f32>) -> (indices: Vec<usize>)
    ensures
        forall|i: int| 0 <= i < indices.len() ==> (indices[i] < a.len() && a[indices[i] as int] != 0.0f32),
        forall|j: int| 0 <= j < a.len() ==> (a[j] != 0.0f32 <==> exists|k: int| 0 <= k < indices.len() && indices[k] == j),
        forall|i1: int, i2: int| 0 <= i1 < i2 < indices.len() ==> indices[i1] < indices[i2],
        forall|i: int, j: int| 0 <= i < j < indices.len() ==> indices[i] != indices[j],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}