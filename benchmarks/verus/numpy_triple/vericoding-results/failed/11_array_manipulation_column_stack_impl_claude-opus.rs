// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn column_stack(arrays: Vec<Vec<f32>>) -> (result: Vec<f32>)
    requires
        arrays.len() > 0,
        forall|i: int| 0 <= i < arrays.len() ==> #[trigger] arrays[i].len() == arrays[0].len(),
    ensures
        result.len() == arrays.len() * arrays[0].len(),
        forall|i: int, j: int| 
            0 <= i < arrays[0].len() && 0 <= j < arrays.len() ==>
            #[trigger] result[j * arrays[0].len() + i] == arrays[j][i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed index bounds checking in invariants */
    let mut result: Vec<f32> = Vec::new();
    let n_rows = arrays[0].len();
    let n_cols = arrays.len();
    
    let mut j: usize = 0;
    while j < n_cols
        invariant
            j <= n_cols,
            result.len() == j * n_rows,
            forall|jj: int, ii: int| 0 <= jj < j && 0 <= ii < n_rows && jj * n_rows + ii < result.len() ==> result[jj * n_rows + ii] == arrays[jj][ii],
            n_rows == arrays[0].len(),
            n_cols == arrays.len(),
            forall|k: int| 0 <= k < arrays.len() ==> #[trigger] arrays[k].len() == n_rows,
        decreases n_cols - j
    {
        let mut i: usize = 0;
        while i < n_rows
            invariant
                i <= n_rows,
                j < n_cols,
                result.len() == j * n_rows + i,
                forall|jj: int, ii: int| 0 <= jj < j && 0 <= ii < n_rows && jj * n_rows + ii < result.len() ==> result[jj * n_rows + ii] == arrays[jj][ii],
                forall|ii: int| 0 <= ii < i && (j as int) * (n_rows as int) + ii < result.len() ==> result[(j as int) * (n_rows as int) + ii] == arrays[j as int][ii],
                n_rows == arrays[0].len(),
                n_cols == arrays.len(),
                forall|k: int| 0 <= k < arrays.len() ==> #[trigger] arrays[k].len() == n_rows,
            decreases n_rows - i
        {
            result.push(arrays[j][i]);
            i = i + 1;
        }
        j = j + 1;
    }
    result
}
// </vc-code>

}
fn main() {}