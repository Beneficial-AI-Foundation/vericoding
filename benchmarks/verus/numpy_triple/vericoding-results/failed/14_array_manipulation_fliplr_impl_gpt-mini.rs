// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compute reversed index */
fn rev_index(len: int, j: int) -> int { len - 1 - j }
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
    /* code modified by LLM (iteration 5): implement fliplr by reversing each row with proper loop invariants */
    let n: int = m.len();
    let row_len: int = m@[0].len();
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: int = 0;
    while i < n
        invariant 0 <= i && i <= n
        invariant result.len() == i
        invariant forall|k: int| 0 <= k < i ==> result@[k].len() == row_len
        invariant forall|k: int, jj: int| 0 <= k < i && 0 <= jj < row_len ==> result@[k]@[jj] == m@[k]@[rev_index(row_len, jj)]
        decreases n - i
    {
        let mut row: Vec<f32> = Vec::new();
        let mut j: int = 0;
        while j < row_len
            invariant 0 <= j && j <= row_len
            invariant row.len() == j
            invariant 0 <= i && i < n
            invariant forall|jj: int| 0 <= jj < j ==> row@[jj] == m@[i]@[rev_index(row_len, jj)]
            decreases row_len - j
        {
            let val: f32 = m@[i]@[rev_index(row_len, j)];
            row.push(val);
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