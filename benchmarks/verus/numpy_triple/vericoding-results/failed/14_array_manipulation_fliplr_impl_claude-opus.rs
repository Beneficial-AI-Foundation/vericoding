// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn fliplr(m: Vec<Vec<f32>>) -> (result: Vec<Vec<f32>>)
    requires 
        m.len() > 0,
        forall|i: int| 0 <= i < m.len() ==> m[i].len() > 0,
        forall|i: int, j: int| 0 <= i < m.len() && 0 <= j < m.len() ==> m[i].len() == m[j].len(),
    ensures
        result.len() == m.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == m[i].len(),
        forall|i: int, j: int| #![trigger result[i][j]] 0 <= i < result.len() && 0 <= j < result[i].len() ==>
            result[i][j] == m[i][(m[i].len() - 1 - j as usize) as int],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed all type mismatches by removing 'as int' from usize comparisons */
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < m.len()
        invariant
            i <= m.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k].len() == m[k].len(),
            forall|k: int, j: int| 0 <= k < i && 0 <= j < result[k].len() ==> result[k][j] == m[k][(m[k].len() - 1 - j as usize) as int],
        decreases m.len() - i
    {
        let mut row: Vec<f32> = Vec::new();
        let mut j: usize = 0;
        let row_len = m[i].len();
        while j < row_len
            invariant
                i < m.len(),
                j <= row_len,
                row_len == m[i].len(),
                row.len() == j,
                forall|k: int| 0 <= k < j ==> row[k] == m[i as int][(row_len - 1 - k as usize) as int],
            decreases row_len - j
        {
            proof {
                assert(i < m.len());
                assert(j < row_len);
                assert(row_len == m[i].len());
                assert(row_len - 1 - j < m[i].len());
            }
            row.push(m[i][row_len - 1 - j]);
            j = j + 1;
        }
        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}