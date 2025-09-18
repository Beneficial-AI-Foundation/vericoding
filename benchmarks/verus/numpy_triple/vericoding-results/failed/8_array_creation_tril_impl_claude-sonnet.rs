// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed helper functions for syntax compatibility */
spec fn matrix_dims_preserved(m: Vec<Vec<f64>>, result: Vec<Vec<f64>>) -> bool {
    result.len() == m.len() &&
    (forall|i: int| 0 <= i < result.len() ==> result[i].len() == m[0].len())
}

proof fn lemma_matrix_construction_preserves_dims(m: Vec<Vec<f64>>, result: Vec<Vec<f64>>)
    requires
        m.len() > 0,
        forall|i: int| 0 <= i < m.len() ==> m[i].len() == m[0].len(),
        result.len() == m.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == m[0].len(),
    ensures
        matrix_dims_preserved(m, result)
{
}
// </vc-helpers>

// <vc-spec>
fn tril(m: Vec<Vec<f64>>, k: i32) -> (result: Vec<Vec<f64>>)
    requires 
        m.len() > 0,
        forall|i: int| 0 <= i < m.len() ==> #[trigger] m[i].len() == m[0].len(),
    ensures
        result.len() == m.len(),
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == m[0].len(),
        forall|i: int, j: int| 
            0 <= i < result.len() && 0 <= j < result[i].len() ==> 
            #[trigger] result[i][j] == if i >= j - k { m[i][j] } else { 0.0 },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type mismatches by using as int conversions in invariants */
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < m.len()
        invariant
            0 <= i <= m.len(),
            result.len() == i,
            forall|idx: int| 0 <= idx < result.len() ==> result[idx].len() == m[0].len(),
            forall|row: int, col: int| 
                0 <= row < result.len() && 0 <= col < result[row].len() ==> 
                result[row][col] == if row >= col - k { m[row][col] } else { 0.0 },
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j: usize = 0;
        while j < m[i].len()
            invariant
                0 <= i < m.len(),
                0 <= j <= m[i].len() as int,
                m[i].len() as int == m[0].len() as int,
                row.len() == j,
                forall|col: int| 
                    0 <= col < row.len() ==> 
                    row[col] == if (i as int) >= (col as int) - (k as int) { m[i as int][col] } else { 0.0 },
        {
            let ghost i_int = i as int;
            let ghost j_int = j as int;
            let ghost k_int = k as int;
            if i_int >= j_int - k_int {
                row.push(m[i][j]);
            } else {
                row.push(0.0);
            }
            j += 1;
        }
        result.push(row);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}