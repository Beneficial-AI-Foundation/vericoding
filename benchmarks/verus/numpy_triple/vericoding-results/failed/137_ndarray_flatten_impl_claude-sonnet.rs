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
    /* code modified by LLM (iteration 5): fix type cast for int conversion */
    let mut result = Vec::new();
    let rows = mat.len();
    let cols = mat[0].len();
    
    for i in 0..rows
        invariant
            result@.len() == i * cols,
            forall|r: int, c: int|
                0 <= r < i && 0 <= c < cols ==> 
                result@[r * cols + c] == mat@[r as usize]@[c]
    {
        for j in 0..cols
            invariant
                result@.len() == i * cols + j,
                forall|r: int, c: int|
                    0 <= r < i && 0 <= c < cols ==>
                    result@[r * cols + c] == mat@[r as usize]@[c],
                forall|c: int|
                    0 <= c < j ==>
                    result@[i * cols + c] == mat@[i]@[c]
        {
            result.push(mat[i][j]);
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}