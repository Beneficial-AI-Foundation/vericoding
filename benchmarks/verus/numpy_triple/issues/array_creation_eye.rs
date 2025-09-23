// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn eye(n: usize) -> (result: Vec<Vec<f32>>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i].len() == n,
        forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> 
            result[i][j] == if i == j { 1.0f32 } else { 0.0f32 },
        forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> 
            result[i][j] == result[j][i],
        forall|i: int| 0 <= i < n ==> exists|j: int| 0 <= j < n && 
            result[i][j] == 1.0f32 && forall|k: int| 0 <= k < n && result[i][k] == 1.0f32 ==> k == j,
        forall|j: int| 0 <= j < n ==> exists|i: int| 0 <= i < n && 
            result[i][j] == 1.0f32 && forall|k: int| 0 <= k < n && result[k][j] == 1.0f32 ==> k == i,
        forall|i: int, j: int| 0 <= i < n && 0 <= j < n && i != j ==> 
            result[i][j] == 0.0f32,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}