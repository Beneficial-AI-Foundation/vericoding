// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): fix exec mode condition by using usize values directly */
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|row_idx: int| 0 <= row_idx < i ==> result[row_idx].len() == m,
            forall|row_idx: int, col_idx: int| 0 <= row_idx < i && 0 <= col_idx < m ==> 
                result[row_idx][col_idx] == if col_idx <= row_idx + (k as int) { 1.0 } else { 0.0 }
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j = 0;
        while j < m
            invariant
                i < n,
                j <= m,
                row.len() == j,
                forall|col_idx: int| 0 <= col_idx < j ==> 
                    row[col_idx] == if col_idx <= (i as int) + (k as int) { 1.0 } else { 0.0 }
        {
            let value = if (j as i32) <= (i as i32) + k { 1.0 } else { 0.0 };
            row.push(value);
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