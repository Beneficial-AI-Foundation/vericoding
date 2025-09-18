// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn fliplr_index_lemma(j: int, len: int)
    requires
        0 <= j < len,
    ensures
        (len - 1 - j) >= 0,
        (len - 1 - j) < len,
        len - 1 - j == (len - 1 - j)
{
}

spec fn is_valid_index(i: int, len: int) -> bool {
    0 <= i < len
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
    /* code modified by LLM (iteration 5): Fixed integer type conversions */
    let mut result: Vec<Vec<f32>> = Vec::new();
    let n = m.len() as int;
    
    let mut i: int = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i as usize,
            forall|k: int| 0 <= k < i ==> result[k as usize].len() == m[k as usize].len(),
            forall|k: int, l: int| 0 <= k < i && 0 <= l < result[k as usize].len() ==> 
                result[k as usize][l as usize] == m[k as usize][(m[k as usize].len() as int - 1 - l)]
    {
        let row_len = m[i as usize].len() as int;
        let mut new_row: Vec<f32> = Vec::new();
        let mut j: int = 0;
        
        while j < row_len
            invariant
                j <= row_len,
                new_row.len() == j as usize,
                forall|l: int| 0 <= l < j ==> new_row[l as usize] == m[i as usize][(row_len - 1 - l)]
        {
            proof { fliplr_index_lemma(j, row_len); }
            let reverse_index = (row_len - 1 - j) as usize;
            let value = m[i as usize][reverse_index];
            new_row.push(value);
            j += 1;
        }
        
        result.push(new_row);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}