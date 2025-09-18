// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added decreases clause to prove loop termination */
fn create_row(n: usize, row_index: usize) -> (row: Vec<f32>)
    requires
        row_index < n,
    ensures
        row.len() == n,
        forall|j: int| 0 <= j < n ==> row[j] == if j == row_index as int { 1.0f32 } else { 0.0f32 },
{
    let mut row: Vec<f32> = Vec::new();
    let mut j: usize = 0;
    while j < n
        invariant
            0 <= j <= n,
            j == row.len(),
            row_index < n,
            forall|k: int| 0 <= k < j ==> row[k] == if k == row_index as int { 1.0f32 } else { 0.0f32 },
        decreases n - j,
    {
        if j == row_index {
            row.push(1.0f32);
        } else {
            row.push(0.0f32);
        }
        j = j + 1;
    }
    row
}
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
{
    /* code modified by LLM (iteration 3): added decreases clause to prove loop termination */
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] result[k].len() == n,
            forall|k: int, l: int| 0 <= k < i && 0 <= l < n ==> 
                result[k][l] == if k == l { 1.0f32 } else { 0.0f32 },
        decreases n - i,
    {
        let row = create_row(n, i);
        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}