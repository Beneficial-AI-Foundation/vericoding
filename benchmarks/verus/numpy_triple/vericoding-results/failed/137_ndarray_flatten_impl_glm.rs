// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add helper function to validate matrix bounds */
fn valid_matrix_index(mat: &Vec<Vec<i8>>, row: usize, col: usize) -> bool
    requires
        mat@.len() > 0,
        forall|i: int| 0 <= i < mat@.len() ==> mat@[i].len() > 0,
        forall|i: int, j: int| 0 <= i < mat@.len() && 0 <= j < mat@.len() ==> mat@[i].len() == mat@[j].len(),
    ensures
        result <==> (0 <= row < mat.len() && 0 <= col < mat[0].len())
{
    row < mat.len() && col < mat[0].len()
}
// </vc-helpers>

// <vc-spec>
fn flatten(mat: Vec<Vec<i8>>) -> (result: Vec<i8>)
    requires 
        mat@.len() > 0,
        forall|i: int| 0 <= i < mat@.len() ==> mat@[i].len() > 0,
        forall|i: int, j: int| 0 <= i < mat@.len() && 0 <= j < mat@.len() ==> mat@[i].len() == mat@[j].len(),
    ensures 
        result@.len() == mat@.len() * mat@[0].len(),
        forall|r: int, c: int| 
            0 <= r < mat@.len() && 0 <= c < mat@[0].len() ==>
            result@[r * mat@[0].len() + c] == mat@[r][c]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix bounds checking and invariant maintenance */
    let num_rows = mat.len();
    let num_cols = mat[0].len();
    let mut result = Vec::new();
    let mut r: usize = 0;
    while r < num_rows
        invariant
            0 <= r <= num_rows as int,
            result@.len() == (r as int) * (num_cols as int),
            forall|i: int, j: int| 
                0 <= i < (r as int) && 0 <= j < (num_cols as int) ==>
                result@[i * (num_cols as int) + j] == mat@[i][j],
        decreases (num_rows as int) - (r as int)
    {
        let mut c: usize = 0;
        while c < num_cols
            invariant
                0 <= c <= num_cols as int,
                result@.len() == (r as int) * (num_cols as int) + (c as int),
                forall|i: int, j: int| 
                    (0 <= i < (r as int) && 0 <= j < (num_cols as int)) || 
                    (i == (r as int) && 0 <= j < (c as int)) ==>
                    result@[i * (num_cols as int) + j] == mat@[i][j],
            decreases (num_cols as int) - (c as int)
        {
            proof {
                assert(valid_matrix_index(&mat, r, c));
            }
            result.push(mat[r][c]);
            c += 1;
        }
        r += 1;
    }
    result
}
// </vc-code>

}
fn main() {}