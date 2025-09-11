// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn broadcast_to(v: Vec<f32>, m: usize) -> (result: Vec<Vec<f32>>)
    requires v.len() > 0,
    ensures
        result.len() == m,

        forall|i: int, j: int| 0 <= i < m && 0 <= j < v.len() ==> result[i][j] == v[j],

        forall|i: int| 0 <= i < m ==> result[i]@ == v@,

        forall|j: int, i1: int, i2: int| 0 <= j < v.len() && 0 <= i1 < m && 0 <= i2 < m ==> result[i1][j] == result[i2][j],

        forall|i: int, j: int| 0 <= i < m && 0 <= j < v.len() ==> exists|k: int| 0 <= k < v.len() && result[i][j] == v[k] && k == j,

        forall|i1: int, i2: int| 0 <= i1 < m && 0 <= i2 < m ==> result[i1]@ == result[i2]@
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}