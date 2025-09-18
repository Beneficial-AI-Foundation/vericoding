// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Removed unnecessary helper section. */
// </vc-helpers>

// <vc-spec>
fn eye(n: usize) -> (result: Vec<Vec<f32>>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> #[trigger] result[i].len() == n,
        forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> 
            result[i][j] == if i == j { 1.0f32 } else { 0.0f32 },
        forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> 
            result[i][j] == result[j][i],
        forall|i: int, j:int| 0 <= i <= j < n ==> (#[trigger] result[i][j] == 1.0f32 ==> i == j),
        forall|i: int, j: int| 0 <= i < n && 0 <= j < n && i != j ==> 
            result[i][j] == 0.0f32,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Corrected loop invariants and logic for array initialization. */
{
    let mut result: Vec<Vec<f32>> = Vec::new();
    let n_usize = n;

    for i_usize in 0..n_usize
        invariant
            0 <= i_usize as int,
            i_usize <= n_usize,
            result.len() == i_usize,
            forall|k: int| 0 <= k < i_usize as int ==> #[trigger] result[k].len() == n_usize,
            forall|k: int, j: int| 0 <= k < i_usize as int && 0 <= j < n_usize as int ==> 
                result[k][j] == if k == j { 1.0f32 } else { 0.0f32 },
    {
        let mut row: Vec<f32> = Vec::new();
        for j_usize in 0..n_usize
            invariant
                0 <= j_usize as int,
                j_usize <= n_usize,
                row.len() == j_usize,
                forall|k: int| 0 <= k < j_usize as int ==> #[trigger] row[k] == if i_usize as int == k { 1.0f32 } else { 0.0f32 },
        {
            if i_usize == j_usize {
                row.push(1.0f32);
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