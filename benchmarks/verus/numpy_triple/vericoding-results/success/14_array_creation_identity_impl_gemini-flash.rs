// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): There are no helper functions, so this is an empty change for the helper block. */
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
/* code modified by LLM (iteration 2): added decreases clauses to loops */
{
    let mut mat: Vec<Vec<f64>> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            mat.len() == i,
            // All rows up to i are initialized
            forall|k: int| 0 <= k < i ==> mat[k].len() == n,
            // Elements in already-initialized rows are correct
            forall|k: int, l: int| 0 <= k < i && 0 <= l < n ==> mat[k][l] == if k == l { 1.0 } else { 0.0 }
        decreases n - i
    {
        let mut row: Vec<f64> = Vec::with_capacity(n);
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                row.len() == j,
                // Elements in the current row up to j are correct
                forall|l: int| 0 <= l < j ==> row[l] == if i as int == l { 1.0 } else { 0.0 }
            decreases n - j
        {
            row.push(if i == j { 1.0 } else { 0.0 });
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