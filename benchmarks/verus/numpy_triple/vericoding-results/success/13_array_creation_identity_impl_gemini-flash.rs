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
/* code modified by LLM (iteration 2): remove shrink_to_fit calls to resolve compilation errors */
{
    let mut mat: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            mat.len() == i,
            // All rows up to i-1 have been initialized correctly
            forall|row_idx: int| 0 <= row_idx < i as int ==> #[trigger] mat[row_idx].len() == n,
            forall|row_idx: int, col_idx: int| 0 <= row_idx < i as int && 0 <= col_idx < n as int ==> 
                #[trigger] mat[row_idx][col_idx] == if row_idx == col_idx { 1.0 } else { 0.0 }
        decreases
            n - i
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                row.len() == j,
                // Elements in the current row up to j-1 are correct
                forall|col_idx: int| 0 <= col_idx < j as int ==> #[trigger] row[col_idx] == if i as int == col_idx { 1.0 } else { 0.0 }
            decreases
                n - j
        {
            if i == j {
                row.push(1.0);
            } else {
                row.push(0.0);
            }
            j = j + 1;
        }
        mat.push(row);
        i = i + 1;
    }
    mat
}
// </vc-code>

}
fn main() {}