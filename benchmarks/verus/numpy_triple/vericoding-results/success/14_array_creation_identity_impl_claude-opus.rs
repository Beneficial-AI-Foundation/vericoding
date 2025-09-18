// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn identity(n: usize) -> (result: Vec<Vec<f64>>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i].len() == n,
        forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==>
            result[i][j] == if i == j { 1.0 } else { 0.0 }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Added decreases clauses to both loops */
    let mut matrix: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            matrix.len() == i,
            forall|k: int| 0 <= k < i ==> matrix[k].len() == n,
            forall|k: int, j: int| 0 <= k < i && 0 <= j < n ==> 
                matrix[k][j] == if k == j { 1.0 } else { 0.0 }
        decreases n - i
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                j <= n,
                row.len() == j,
                forall|k: int| 0 <= k < j ==> 
                    row[k] == if i == k { 1.0 } else { 0.0 }
            decreases n - j
        {
            if i == j {
                row.push(1.0);
            } else {
                row.push(0.0);
            }
            j = j + 1;
        }
        matrix.push(row);
        i = i + 1;
    }
    matrix
}
// </vc-code>

}
fn main() {}