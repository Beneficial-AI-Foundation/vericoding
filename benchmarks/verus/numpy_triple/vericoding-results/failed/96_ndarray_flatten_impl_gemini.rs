// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn flatten(mat: Vec<Vec<f32>>) -> (result: Vec<f32>)
    requires 
        mat.len() > 0,
        forall|i: int| 0 <= i < mat.len() ==> mat[i].len() > 0,
        forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat.len() ==> mat[i].len() == mat[j].len(),
    ensures 
        result.len() == mat.len() * mat[0].len(),
        forall|r: int, c: int| 
            0 <= r < mat.len() && 0 <= c < mat[0].len() ==>
            result[r * mat[0].len() + c] == mat[r][c]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): add assertions and carry over preconditions in invariants */
{
    let num_rows = mat.len();
    let num_cols = mat[0].len();
    let mut flat_vec = Vec::new();

    let mut r: usize = 0;
    while r < num_rows
        invariant
            0 <= r <= num_rows,
            flat_vec.len() == r * num_cols,
            forall|i: int, j: int|
                0 <= i < (r as int) && 0 <= j < (num_cols as int) ==> 
                flat_vec[i * (num_cols as int) + j] == mat[i][j],
            // Carry over function preconditions into the loop
            mat.len() == num_rows,
            mat.len() > 0 ==> mat[0].len() == num_cols,
            forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat.len() ==> mat[i].len() == mat[j].len(),
        decreases num_rows - r
    {
        let mut c: usize = 0;
        while c < num_cols
            invariant
                0 <= r < num_rows,
                0 <= c <= num_cols,
                flat_vec.len() == r * num_cols + c,
                forall|i: int, j: int|
                    0 <= i < (r as int) && 0 <= j < (num_cols as int) ==> 
                    flat_vec[i * (num_cols as int) + j] == mat[i][j],
                forall|j: int|
                    0 <= j < (c as int) ==> 
                    flat_vec[(r as int) * (num_cols as int) + j] == mat[r as int][j],
                // Carry over facts for the inner loop
                mat.len() == num_rows,
                mat.len() > 0 ==> mat[0].len() == num_cols,
                forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat.len() ==> mat[i].len() == mat[j].len(),
            decreases num_cols - c
        {
            assert(mat[r].len() == num_cols); // Justify access to mat[r][c]
            flat_vec.push(mat[r][c]);
            c = c + 1;
        }
        
        r = r + 1;
    }
    
    flat_vec
}
// </vc-code>

}
fn main() {}