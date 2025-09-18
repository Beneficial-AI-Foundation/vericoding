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
    /* code modified by LLM (iteration 4): Fix compilation errors by using `result@.len()` and `int` for sequence indexing. */
    let num_rows = arrays.len();
    let num_cols = arrays[0].len();
    let mut result = Vec::with_capacity(num_rows * num_cols);

    let mut j: usize = 0;
    while j < num_rows
        invariant
            num_rows == arrays.len(),
            num_cols == arrays[0].len(),
            forall|k: int| 0 <= k < arrays.len() ==> #[trigger] arrays[k].len() == num_cols,
            0 <= j <= num_rows,
            result@.len() == (j as nat) * (num_cols as nat),
            forall|row: int, col: int|
                0 <= row < j as int && 0 <= col < num_cols as int ==>
                #[trigger] result@[row * (num_cols as int) + col] == arrays@[row]@[col],
        decreases num_rows - j
    {
        let mut i: usize = 0;
        while i < num_cols
            invariant
                num_rows == arrays.len(),
                num_cols == arrays[0].len(),
                forall|k: int| 0 <= k < arrays.len() ==> #[trigger] arrays[k].len() == num_cols,
                j < num_rows,
                0 <= i <= num_cols,
                result@.len() == (j as nat) * (num_cols as nat) + (i as nat),
                // property for fully processed rows
                forall|row: int, col: int|
                    0 <= row < j as int && 0 <= col < num_cols as int ==>
                    #[trigger] result@[row * (num_cols as int) + col] == arrays@[row]@[col],
                // property for columns in the current row
                forall|col: int|
                    0 <= col < i as int ==>
                    #[trigger] result@[(j as int) * (num_cols as int) + col] == arrays@[j as int]@[col],
            decreases num_cols - i
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