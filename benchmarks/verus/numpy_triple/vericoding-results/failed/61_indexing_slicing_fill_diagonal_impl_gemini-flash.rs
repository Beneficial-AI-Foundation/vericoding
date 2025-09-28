// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [Fixed `create_t_vec` return type to `Vec<T>` as `int` type is for ghost code.] */
fn create_t_vec<T>(len: int, init_val: T) -> (v: Vec<T>)
{
    let mut v_local = Vec::new();
    let mut i = 0;
    while i < len
        invariant
            0 <= i <= len,
            v_local@.len() == i,
            forall|j: int| 0 <= j < i ==> v_local@[j] == init_val,
    {
        v_local.push(init_val);
        i = i + 1;
    }
    v_local
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
/* code modified by LLM (iteration 5): [Fixed compilation error by changing `r_idx as int < num_rows as int,` to `r_idx as int < num_rows as int` in the inner loop's invariant block.] */
{
    let mut result: Vec<Vec<T>> = Vec::new();
    let num_rows: usize = mat.len();
    let num_cols: usize = if num_rows > 0 { mat[0].len() } else { 0 };

    let mut r_idx: usize = 0;
    while r_idx < num_rows
        invariant
            0 <= r_idx as int <= num_rows as int,
            result@.len() == r_idx as int,
            forall|k: int| 0 <= k < r_idx as int ==> result@[k].len() == num_cols as int,
            forall|k: int, j: int| 0 <= k < r_idx as int && 0 <= j < num_cols as int
                ==> (k == j ==> result@[k][j] == val)
                && (k != j ==> result@[k][j] == mat@[k][j]),
            mat@.len() == num_rows as int,
            forall|i: int| 0 <= i < mat@.len() ==> mat@[i].len() == num_cols as int,
    {
        let mut current_row: Vec<T> = Vec::new();
        let mut c_idx: usize = 0;
        while c_idx < num_cols
            invariant
                0 <= c_idx as int <= num_cols as int,
                current_row@.len() == c_idx as int,
                0 <= r_idx as int,
                r_idx as int < num_rows as int,
                mat@[r_idx as int].len() == num_cols as int,
                forall|k: int| 0 <= k < c_idx as int
                    ==> (r_idx as int == k ==> current_row@[k] == val)
                    && (r_idx as int != k ==> current_row@[k] == mat@[r_idx as int][k])

        {
            if r_idx == c_idx {
                current_row.push(val);
            } else {
                current_row.push(mat[r_idx][c_idx]);
            }
            c_idx = c_idx + 1;
        }
        result.push(current_row);
        r_idx = r_idx + 1;
    }
    result
}
// </vc-code>

}
fn main() {}