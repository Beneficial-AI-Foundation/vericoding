// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): create zero-initialized 3D Vec for f32 */
fn vec3_new_f32(k: usize, rows: usize, cols: usize) -> Vec<Vec<Vec<f32>>> {
    let mut res: Vec<Vec<Vec<f32>>> = Vec::new();
    let mut i: usize = 0;
    while i < k {
        decreases(k - i);
        let mut mid: Vec<Vec<f32>> = Vec::new();
        let mut j: usize = 0;
        while j < rows {
            decreases(rows - j);
            let mut row: Vec<f32> = Vec::new();
            let mut l: usize = 0;
            while l < cols {
                decreases(cols - l);
                row.push(0.0f32);
                l += 1;
            }
            mid.push(row);
            j += 1;
        }
        res.push(mid);
        i += 1;
    }
    res
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
    /* code modified by LLM (iteration 5): build splits by initializing k empty mids and filling by cloning rows; use int indices in proof blocks */
    let n = mat.len();
    let rows_per = n / k;
    let cols = mat[0].len();

    let mut result: Vec<Vec<Vec<f32>>> = Vec::new();

    // initialize result with k empty mids
    let mut i: usize = 0;
    while i < k {
        decreases(k - i);
        result.push(Vec::new());
        i += 1;
    }

    // fill mids by iterating global row index
    let mut global: usize = 0;
    let mut split_idx: usize = 0;
    while split_idx < k {
        decreases(k - split_idx);
        let mut mid: Vec<Vec<f32>> = Vec::new();
        let mut row_idx: usize = 0;
        while row_idx < rows_per {
            decreases(rows_per - row_idx + k - split_idx);
            mid.push(mat[global].clone());
            global += 1;
            row_idx += 1;
        }
        proof {
            assert(mid.len() == rows_per);
        }
        result[split_idx] = mid;
        split_idx += 1;
    }

    // final checks in a proof block using int indices for Vec indexing in specs
    proof {
        assert(global == n);
        assert(result.len() == k);
        let mut si: int = 0;
        while si < k as int {
            decreases(k as int - si);
            assert(result[si].len() == rows_per);
            si += 1;
        }
    }

    result
}
// </vc-code>

}
fn main() {}