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
    /* code modified by LLM (iteration 3): Added decreases clauses to both loops */
    let n = v.len();
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == v@.len(),
            result@.len() == i as int,
            forall|k: int| 0 <= k < i ==> result@[k].len() == n as int,
            forall|k: int, j: int| 0 <= k < i && 0 <= j < n && k == j ==> result@[k][j] == v@[k],
            forall|k: int, j: int| 0 <= k < i && 0 <= j < n && k != j ==> result@[k][j] == 0.0f32,
        decreases n - i
    {
        let mut row: Vec<f32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == v@.len(),
                row@.len() == j as int,
                forall|k: int| 0 <= k < j && k == i as int ==> row@[k] == v@[i as int],
                forall|k: int| 0 <= k < j && k != i as int ==> row@[k] == 0.0f32,
            decreases n - j
        {
            if i == j {
                row.push(v[i]);
            } else {
                row.push(0.0f32);
            }
            j = j + 1;
        }
        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}