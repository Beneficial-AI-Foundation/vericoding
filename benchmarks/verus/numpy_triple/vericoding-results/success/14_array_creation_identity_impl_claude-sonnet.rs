// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added decreases clause to while loop */
spec fn is_identity_matrix(matrix: Vec<Vec<f64>>, n: usize) -> bool {
    matrix.len() == n &&
    (forall|i: int| 0 <= i < n ==> matrix[i].len() == n) &&
    (forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> matrix[i][j] == if i == j { 1.0 } else { 0.0 })
}

fn create_row(n: usize, row_index: usize) -> (result: Vec<f64>)
    requires row_index < n
    ensures
        result.len() == n,
        forall|j: int| 0 <= j < n ==> result[j] == if row_index == j { 1.0 } else { 0.0 }
{
    let mut row = Vec::new();
    let mut j = 0;
    while j < n
        invariant
            j <= n,
            row.len() == j,
            forall|k: int| 0 <= k < j ==> row[k] == if row_index == k { 1.0 } else { 0.0 }
        decreases n - j
    {
        if j == row_index {
            row.push(1.0);
        } else {
            row.push(0.0);
        }
        j += 1;
    }
    row
}
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
    /* code modified by LLM (iteration 3): added decreases clause to while loop */
    let mut matrix: Vec<Vec<f64>> = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            i <= n,
            matrix.len() == i,
            forall|k: int| 0 <= k < i ==> matrix[k].len() == n,
            forall|k: int, j: int| 0 <= k < i && 0 <= j < n ==> matrix[k][j] == if k == j { 1.0 } else { 0.0 }
        decreases n - i
    {
        let row = create_row(n, i);
        matrix.push(row);
        i += 1;
    }
    matrix
}
// </vc-code>

}
fn main() {}