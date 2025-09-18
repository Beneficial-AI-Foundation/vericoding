// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed proof function syntax to use executable code */
spec fn split_index_valid(orig_row: int, k: int, mat_len: int) -> bool
{
    k > 0 && mat_len > 0 && mat_len % k == 0 &&
    {
        let split_idx = orig_row / (mat_len / k);
        let row_idx = orig_row % (mat_len / k);
        0 <= split_idx < k && 0 <= row_idx < mat_len / k
    }
}

proof fn division_properties(mat_len: int, k: int)
    requires k > 0, mat_len > 0, mat_len % k == 0
    ensures forall|i: int| #![trigger i / (mat_len / k), i % (mat_len / k)] 0 <= i < mat_len ==> {
        let split_idx = i / (mat_len / k);
        let row_idx = i % (mat_len / k);
        0 <= split_idx < k && 0 <= row_idx < mat_len / k && i == split_idx * (mat_len / k) + row_idx
    }
{
    let chunk_size = mat_len / k;
    assert(chunk_size > 0);
}
// </vc-helpers>

// <vc-spec>
fn vsplit(mat: Vec<Vec<f32>>, k: usize) -> (result: Vec<Vec<Vec<f32>>>)
    requires 
        k > 0,
        mat.len() > 0,
        mat.len() % k == 0,
        forall|i: int| #![trigger mat[i]] 0 <= i < mat.len() ==> mat[i].len() == mat[0].len(),
    ensures
        result.len() == k,
        forall|split_idx: int| #![trigger result[split_idx]] 0 <= split_idx < k ==> result[split_idx].len() == mat.len() / k,
        forall|split_idx: int, row_idx: int, col_idx: int| #![trigger result[split_idx][row_idx][col_idx]]
            0 <= split_idx < k && 0 <= row_idx < mat.len() / k && 0 <= col_idx < mat[0].len() ==>
            exists|global_row: int| 
                global_row == split_idx * (mat.len() / k) + row_idx &&
                0 <= global_row < mat.len() &&
                result[split_idx][row_idx][col_idx] == #[trigger] mat[global_row][col_idx],
        forall|orig_row: int| #![trigger mat[orig_row]] 0 <= orig_row < mat.len() ==>
            exists|split_idx: int, row_idx: int|
                0 <= split_idx < k && 0 <= row_idx < mat.len() / k &&
                orig_row == #[trigger] (split_idx * (mat.len() / k) + row_idx),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed syntax error with curly braces in invariant */
    let chunk_size = (mat.len() / k) as usize;
    let mut result: Vec<Vec<Vec<f32>>> = Vec::new();
    
    proof {
        division_properties(mat.len() as int, k as int);
    }
    
    for split_idx in 0..k
        invariant
            result.len() == split_idx,
            forall|s: int| #![trigger result[s]] 0 <= s < split_idx ==> result[s].len() == chunk_size,
            forall|s: int, r: int, c: int| #![trigger result[s][r][c]]
                0 <= s < split_idx && 0 <= r < chunk_size && 0 <= c < mat@[0].len() ==> {
                    let global_row = s * chunk_size + r;
                    0 <= global_row < mat.len() &&
                    result[s][r][c] == mat[global_row as int][c]
                }
    {
        let mut chunk: Vec<Vec<f32>> = Vec::new();
        
        for row_idx in 0..chunk_size
            invariant
                chunk.len() == row_idx,
                forall|r: int, c: int| #![trigger chunk[r][c]]
                    0 <= r < row_idx && 0 <= c < mat@[0].len() ==> {
                        let global_row = split_idx * chunk_size + r;
                        0 <= global_row < mat.len() &&
                        chunk[r][c] == mat[global_row as int][c]
                    }
        {
            let global_row = split_idx * chunk_size + row_idx;
            
            proof {
                assert(split_idx < k);
                assert(row_idx < chunk_size);
                assert(global_row < mat.len());
            }
            
            chunk.push(mat[global_row].clone());
        }
        
        result.push(chunk);
    }
    
    result
}
// </vc-code>

}
fn main() {}