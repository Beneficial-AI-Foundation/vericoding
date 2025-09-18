// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helpers needed, unchanged */
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
    /* code modified by LLM (iteration 5): fixed type mismatches by casting lengths to int, fixed indexing syntax to use @[i] for nested sequences */
    let rows: int = mat.len() as int;
    let cols: int = mat[0].len() as int;
    let mut result: Vec<f32> = Vec::new();
    let mut r: int = 0;
    while r < rows
        decreases rows - r
    {
        let mut c: int = 0;
        while c < cols
            decreases cols - c
        {
            proof {
                assert(r >= 0 && r < rows);
                assert(c >= 0 && c < cols);
            }
            let elem = mat@[r]@[c];
            result.push(elem);
            c = c + 1;
        }
        r = r + 1;
    }
    result
}
// </vc-code>

}
fn main() {}