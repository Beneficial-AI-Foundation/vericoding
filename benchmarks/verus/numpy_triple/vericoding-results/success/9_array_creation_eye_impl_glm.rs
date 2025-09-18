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
/* code modified by LLM (iteration 3): Added decreases clause to loops */
{
    let mut result: Vec<Vec<f32>> = Vec::with_capacity(n);
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] result[k].len() == n,
            forall|k: int, j: int| 0 <= k < i && 0 <= j < n ==> 
                result[k][j] == if k == j { 1.0f32 } else { 0.0f32 },
        decreases n - i,
    {
        let mut row: Vec<f32> = Vec::with_capacity(n);
        let mut col = 0;
        while col < n
            invariant
                0 <= col <= n,
                row.len() == col,
                forall|k: int| 0 <= k < col ==> 
                    row[k] == if i == k { 1.0f32 } else { 0.0f32 },
            decreases n - col,
        {
            if col == i {
                row.push(1.0f32);
            } else {
                row.push(0.0f32);
            }
            col += 1;
        }
        result.push(row);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}