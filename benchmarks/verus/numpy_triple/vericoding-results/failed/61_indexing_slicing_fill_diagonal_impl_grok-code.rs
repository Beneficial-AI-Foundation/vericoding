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
    /* code modified by LLM (iteration 5): Fixed compilation errors by removing invalid 'as int' casts in exec code and using direct usize comparisons */
    let mut result: Vec<Vec<T>> = Vec::new();
    let mut i = 0usize;
    let length = mat.len();
    // removed invalid int casts in exec code
    // let length_int = length as int;
    // let diagonal_val_int = 0 as int;  // unused
    proof {
        assert(forall|i: int| 0 <= i < mat@.len() ==> #[trigger] mat@[i].len() == mat@[0].len());
    }
    let mut row_length: usize = 0;
    proof {
        row_length = mat@[0].len() as usize;
    }
    while i < length
        invariant
            result.len() == i,
            forall|ii: int| 0 <= ii < (i as int) ==> #[trigger] result@[ii].len() == mat@[ii].len(),
            forall|ii: int, jj: int| 0 <= ii < (i as int) && 0 <= jj < result@[ii].len() && ii == jj ==> #[trigger] result@[ii][jj] == val,
            forall|ii: int, jj: int| 0 <= ii < (i as int) && 0 <= jj < result@[ii].len() && ii != jj ==> #[trigger] result@[ii][jj] == mat@[ii][jj],
        decreases length - i
    {
        let mut row: Vec<T> = Vec::new();
        let mut j = 0usize;
        while j < row_length
            invariant
                row.len() == j,
                if (i == j) {  // fixed: use direct usize comparison
                    forall|jj: int| 0 <= jj < (j as int) ==> #[trigger] row@[jj] == val
                } else {
                    forall|jj: int| 0 <= jj < (j as int) ==> #[trigger] row@[jj] == mat@[(i as int)][jj]
                },
            decreases row_length - j
        {
            if i == j {  // fixed: use direct usize comparison
                row.push(val);
            } else {
                row.push(mat[i][j]);
            }
            j += 1;
        }
        result.push(row);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}