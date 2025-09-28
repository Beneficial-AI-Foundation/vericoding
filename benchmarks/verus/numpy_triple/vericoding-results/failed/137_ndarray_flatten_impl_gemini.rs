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
    /* code modified by LLM (iteration 5): [refined invariants for nested loops] */
    let rows = mat.len();
    let cols = mat[0].len();

    let mut result: Vec<i8> = Vec::new();

    let mut r: usize = 0;
    while r < rows
        invariant
            0 <= r <= rows,
            rows == mat.len(),
            cols == mat[0].len(),
            forall|i: int| 0 <= i < mat@.len() ==> mat@[i].len() == cols,
            result@.len() == (r as int) * (cols as int),
            forall|i: int, j: int|
                0 <= i < r as int && 0 <= j < cols as int ==>
                result@[i * (cols as int) + j] == mat@[i][j],
        decreases rows - r
    {
        let mut c: usize = 0;
        while c < cols
            invariant
                r < rows,
                0 <= c <= cols,
                rows == mat.len(),
                cols == mat[0].len(),
                forall|i: int| 0 <= i < mat@.len() ==> mat@[i].len() == cols,
                result@.len() == (r as int) * (cols as int) + (c as int),
                forall|i: int, j: int|
                    0 <= i < r as int && 0 <= j < cols as int ==>
                    result@[i * (cols as int) + j] == mat@[i][j],
                forall|j: int|
                    0 <= j < c as int ==>
                    result@[(r as int) * (cols as int) + j] == mat@[r as int][j],
            decreases cols - c
        {
            result.push(mat[r][c]);
            c = c + 1;
        }
        r = r + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}