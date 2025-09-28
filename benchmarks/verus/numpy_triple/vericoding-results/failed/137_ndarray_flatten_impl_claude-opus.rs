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
    /* code modified by LLM (iteration 3): add decreases clauses to loops */
    let rows = mat.len();
    let cols = mat[0].len();
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < rows
        invariant
            i <= rows,
            rows == mat@.len(),
            cols == mat@[0].len(),
            result@.len() == (i as int) * (cols as int),
            forall|r: int, c: int| 
                0 <= r < (i as int) && 0 <= c < (cols as int) ==> 
                result@[r * (cols as int) + c] == mat@[r][c],
        decreases rows - i
    {
        let mut j: usize = 0;
        while j < cols
            invariant
                j <= cols,
                i < rows,
                rows == mat@.len(),
                cols == mat@[0].len(),
                result@.len() == (i as int) * (cols as int) + (j as int),
                forall|r: int, c: int| 
                    0 <= r < (i as int) && 0 <= c < (cols as int) ==> 
                    result@[r * (cols as int) + c] == mat@[r][c],
                forall|c: int|
                    0 <= c < (j as int) ==> 
                    result@[(i as int) * (cols as int) + c] == mat@[i as int][c],
            decreases cols - j
        {
            result.push(mat[i][j]);
            j = j + 1;
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}