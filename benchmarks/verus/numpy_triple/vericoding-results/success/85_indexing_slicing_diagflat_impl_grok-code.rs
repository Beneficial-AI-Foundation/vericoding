// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn diagflat(v: Vec<f32>) -> (result: Vec<Vec<f32>>)
    requires v@.len() > 0,
    ensures
        result@.len() == v@.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == v@.len(),
        forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() && i == j ==> result@[i][j] == v@[i],
        forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() && i != j ==> result@[i][j] == 0.0f32,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): added bounds to invariants to satisfy preconditions and fix recommendation issues */
    let n = v.len();
    let mut result: Vec<Vec<f32>> = Vec::new();
    for i in 0..n
        invariant
            result@.len() == i,
            n == v@.len(),
            forall |k:int| 0 <= k < i ==> result@[k].len() == n,
            forall |k:int, j:int| 0 <= k < i && 0 <= k < v@.len() && 0 <= j < n && k == j ==> result@[k][j] == v@[k],
            forall |k:int, j:int| 0 <= k < i && 0 <= j < n && k != j ==> result@[k][j] == 0.0f32,
    {
        let mut row: Vec<f32> = Vec::new();
        for j in 0..n
            invariant
                row@.len() == j,
                0 <= i < v@.len(),
                forall |m:int| 0 <= m < j && 0 <= m < v@.len() && m != i ==> row@[m] == 0.0f32,
                forall |m:int| 0 <= m < j && 0 <= m < v@.len() && m == i ==> row@[m] == v@[i as int],
        {
            if i == j {
                row.push(v[i]);
            } else {
                row.push(0.0f32);
            }
        }
        result.push(row);
    }
    result
}
// </vc-code>


}
fn main() {}