// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed unnecessary helper function */
// </vc-helpers>

// <vc-spec>
fn fill_diagonal<T: Copy>(mat: Vec<Vec<T>>, val: T) -> (result: Vec<Vec<T>>)
    requires 
        mat@.len() > 0,
        forall|i: int| 0 <= i < mat@.len() ==> #[trigger] mat@[i].len() == mat@[0].len(),
    ensures
        result@.len() == mat@.len(),
        forall|i: int| 0 <= i < result@.len() ==> #[trigger] result@[i].len() == mat@[i].len(),

        forall|i: int, j: int| 
            0 <= i < result@.len() && 0 <= j < result@[i].len() && i == j 
            ==> #[trigger] result@[i][j] == val,

        forall|i: int, j: int| 
            0 <= i < result@.len() && 0 <= j < result@[i].len() && i != j 
            ==> #[trigger] result@[i][j] == mat@[i][j]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error by using direct indexing without get_mut */
    let mut result = mat;
    let n = result.len();
    
    for i in 0..n
        invariant
            result@.len() == mat@.len(),
            forall|k: int| 0 <= k < result@.len() ==> #[trigger] result@[k].len() == mat@[k].len(),
            forall|row: int, col: int|
                0 <= row < result@.len() && 0 <= col < result@[row].len() && row == col && row < i
                ==> #[trigger] result@[row][col] == val,
            forall|row: int, col: int|
                0 <= row < result@.len() && 0 <= col < result@[row].len() && row != col
                ==> #[trigger] result@[row][col] == mat@[row][col],
            forall|row: int, col: int|
                0 <= row < result@.len() && 0 <= col < result@[row].len() && row == col && row >= i
                ==> #[trigger] result@[row][col] == mat@[row][col]
    {
        if i < result[i].len() {
            result[i].set(i, val);
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}