// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): trivial preservation of row lengths */
fn rows_len_preserved<T: Copy>(mat: &Vec<Vec<T>>)
    requires
        mat@.len() > 0,
        forall|i: int| 0 <= i < mat@.len() ==> #[trigger] mat@[i].len() == mat@[0].len(),
    ensures
        forall|i: int| 0 <= i < mat@.len() ==> #[trigger] mat@[i].len() == mat@[0].len(),
{
    proof {
        // The postcondition is identical to the precondition; nothing to prove
    }
}
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
    /* code modified by LLM (iteration 5): clone rows and set diagonal entries */
    let mut result: Vec<Vec<T>> = Vec::new();
    let n: usize = mat.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
        decreases n - i
    {
        let mut row = mat[i].clone();
        let row_len: usize = row.len();
        if i < row_len {
            row[i] = val;
        }
        result.push(row);
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}