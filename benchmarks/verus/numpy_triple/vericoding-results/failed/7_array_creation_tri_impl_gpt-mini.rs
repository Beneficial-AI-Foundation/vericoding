// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): tri_cell predicate */
spec fn tri_cell(i: int, j: int, k: int) -> f64 { if j <= i + k { 1.0 } else { 0.0 } }
/* helper modified by LLM (iteration 5): tri_row_ok predicate */
spec fn tri_row_ok(row: Vec<f64>, i: int, m: int, k: int) -> bool { row.len() == m && (forall|jj: int| 0 <= jj && jj < m as int ==> row[jj as usize] == tri_cell(i, jj, k)) }
// </vc-helpers>

// <vc-spec>
fn tri(n: usize, m: usize, k: i32) -> (result: Vec<Vec<f64>>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i].len() == m,
        forall|i: int, j: int| 0 <= i < n && 0 <= j < m ==> 
            result[i][j] == if j <= i + k { 1.0 } else { 0.0 }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): construct n x m matrix with triangular pattern and maintain invariants */
    let mut res: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant res.len() == i,
        invariant (forall|ii: int| 0 <= ii && ii < i as int ==> (res[ii as usize].len() == m && (forall|jj: int| 0 <= jj && jj < m as int ==> res[ii as usize][jj as usize] == tri_cell(ii, jj, k as int)))),
        decreases n - i
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j: usize = 0;
        while j < m
            invariant row.len() == j,
            invariant (forall|jj: int| 0 <= jj && jj < j as int ==> row[jj as usize] == tri_cell(i as int, jj, k as int)),
            decreases m - j
        {
            let val: f64 = if (j as int) <= (i as int) + (k as int) { 1.0 } else { 0.0 };
            row.push(val);
            j += 1;
        }
        res.push(row);
        i += 1;
    }
    res
}
// </vc-code>

}
fn main() {}