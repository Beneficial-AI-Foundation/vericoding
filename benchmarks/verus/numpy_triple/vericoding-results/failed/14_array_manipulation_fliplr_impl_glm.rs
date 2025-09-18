// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn flip_index(len: int, j: int) -> int
    requires 0 <= j < len,
    ensures 0 <= flip_index(len, j) < len,
    ensures flip_index(len, j) == len - 1 - j
{
    len - 1 - j
}
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
    let mut result = Vec::new();
    let m_len = m.len();
    let row_len = m[0].len();
    
    for i in 0..m_len {
        let mut new_row = Vec::with_capacity(row_len);
        for j in 0..row_len {
            let flipped_j = (row_len - 1 - j) as int;
            new_row.push(m[i][flipped_j as usize]);
        }
        result.push(new_row);
    }
    
    result
}
// </vc-code>

}
fn main() {}