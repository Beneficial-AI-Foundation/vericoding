// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 3): Added decreases clause to both loops */
    let mut result: Vec<Vec<T>> = Vec::new();
    let n = mat.len();
    
    let mut i: usize = 0;
    while i < n
        invariant
            result@.len() == i as int,
            forall|k: int| 0 <= k < i ==> #[trigger] result@[k].len() == mat@[k].len(),
            forall|k: int, j: int| 
                0 <= k < i && 0 <= j < result@[k].len() && k == j 
                ==> #[trigger] result@[k][j] == val,
            forall|k: int, j: int| 
                0 <= k < i && 0 <= j < result@[k].len() && k != j 
                ==> #[trigger] result@[k][j] == mat@[k][j],
        decreases n - i
    {
        let mut new_row: Vec<T> = Vec::new();
        let row_len = mat[i].len();
        
        let mut j: usize = 0;
        while j < row_len
            invariant
                new_row@.len() == j as int,
                forall|k: int| 0 <= k < j && i == k ==> #[trigger] new_row@[k] == val,
                forall|k: int| 0 <= k < j && i != k ==> #[trigger] new_row@[k] == mat@[i as int][k],
            decreases row_len - j
        {
            if i == j {
                new_row.push(val);
            } else {
                new_row.push(mat[i][j]);
            }
            j = j + 1;
        }
        
        result.push(new_row);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}