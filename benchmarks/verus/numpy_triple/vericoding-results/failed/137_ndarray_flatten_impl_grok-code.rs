// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Fixed ghost type usage in exec code by accessing mat.len() and mat[i].len() directly as usize, corrected decreases to use int casts */
    let mut result = Vec::new();
    let mut i: usize = 0;
    let mat_len_usize = mat.len();
    let row_len_usize = mat[0].len();
    while i < mat_len_usize
        invariant
            i <= mat_len_usize,
            result@.len() == (i as int) * mat@[0].len(),
            forall|r: int, c: int| r < (i as int) && c < mat@[0].len() ==> result@[r * mat@[0].len() + c] == mat@[r][c],
        decreases (mat_len_usize - i) as int
    {
        let mut j: usize = 0;
        let inner_len_usize = mat[i].len();
        while j < inner_len_usize
            invariant
                j <= inner_len_usize,
                forall|k: int| k < (j as int) ==> result@[(i as int) * mat@[0].len() + k] == mat@[i as int][k],
            decreases (inner_len_usize - j) as int
        {
            result.push(mat[i][j]);
            j += 1;
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}