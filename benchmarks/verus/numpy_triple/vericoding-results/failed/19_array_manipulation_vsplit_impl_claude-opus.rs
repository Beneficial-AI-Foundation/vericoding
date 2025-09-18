// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Fixed syntax error in assert statement */
    let n = mat.len();
    let chunk_size = n / k;
    let mut result: Vec<Vec<Vec<f32>>> = Vec::new();
    let mut split_idx: usize = 0;
    
    while split_idx < k
        invariant
            0 <= split_idx <= k,
            result.len() == split_idx,
            n == mat.len(),
            chunk_size == n / k,
            k > 0,
            n % k == 0,
            chunk_size > 0,
            split_idx <= k,
            split_idx as int * chunk_size as int <= n as int,
            forall|i: int| #![trigger mat[i]] 0 <= i < mat.len() ==> mat[i].len() == mat[0].len(),
            forall|i: int| #![trigger result[i]] 0 <= i < split_idx ==> result[i].len() == chunk_size,
            forall|i: int, j: int, c: int| #![trigger result[i][j][c]]
                0 <= i < split_idx && 0 <= j < chunk_size && 0 <= c < mat[0].len() ==>
                result[i][j][c] == mat[i * chunk_size + j][c],
        decreases k - split_idx
    {
        let mut chunk: Vec<Vec<f32>> = Vec::new();
        let mut row_idx: usize = 0;
        
        while row_idx < chunk_size
            invariant
                0 <= row_idx <= chunk_size,
                chunk.len() == row_idx,
                0 <= split_idx < k,
                chunk_size == n / k,
                split_idx as int * chunk_size as int + row_idx as int <= n as int,
                forall|i: int| #![trigger mat[i]] 0 <= i < mat.len() ==> mat[i].len() == mat[0].len(),
                forall|j: int, c: int| #![trigger chunk[j][c]]
                    0 <= j < row_idx && 0 <= c < mat[0].len() ==>
                    chunk[j][c] == mat[split_idx * chunk_size + j][c],
            decreases chunk_size - row_idx
        {
            let global_row = split_idx * chunk_size + row_idx;
            proof {
                assert(global_row < n);
                assert(0 <= global_row < mat.len());
            }
            let row = mat[global_row].clone();
            chunk.push(row);
            row_idx = row_idx + 1;
        }
        
        result.push(chunk);
        split_idx = split_idx + 1;
    }
    
    proof {
        assert(result.len() == k);
        assert forall|i: int| #![trigger result[i]] 0 <= i < k implies result[i].len() == chunk_size by {
            assert(result[i].len() == chunk_size);
        }
        assert forall|i: int, j: int, c: int| #![trigger result[i][j][c]]
            0 <= i < k && 0 <= j < chunk_size && 0 <= c < mat[0].len() implies
            result[i][j][c] == mat[i * chunk_size + j][c] by {
                assert(result[i][j][c] == mat[i * chunk_size + j][c]);
            }
    }
    
    result
}
// </vc-code>

}
fn main() {}