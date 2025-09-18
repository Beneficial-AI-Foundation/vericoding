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
{
    /* code modified by LLM (iteration 5): Fixed indexing to use proper Verus syntax */
    let mut result = Vec::new();
    let rows = mat.len();
    let cols = mat[0].len();
    
    let mut i: usize = 0;
    while i < rows
        invariant
            0 <= i <= rows,
            result@.len() == i * cols,
            forall|r: int, c: int| 
                0 <= r < i && 0 <= c < cols ==> 
                result@[r * cols + c] == mat@[r]@[c]
        decreases rows - i
    {
        let mut j: usize = 0;
        while j < cols
            invariant
                0 <= i < rows,
                0 <= j <= cols,
                result@.len() == i * cols + j,
                forall|r: int, c: int| 
                    0 <= r < i && 0 <= c < cols ==> 
                    result@[r * cols + c] == mat@[r]@[c],
                forall|c: int|
                    0 <= c < j ==>
                    result@[i * cols + c] == mat@[i as int]@[c]
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