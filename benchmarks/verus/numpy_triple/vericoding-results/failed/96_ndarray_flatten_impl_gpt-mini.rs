// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): min_nat for nat comparisons */
fn min_nat(a: nat, b: nat) -> nat { if a < b { a } else { b } }
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
    /* code modified by LLM (iteration 5): flatten rows-major traversal with invariants */
    let rows: nat = mat.len();
    let cols: nat = mat[0].len();
    let mut result: Vec<f32> = Vec::new();

    let mut r: nat = 0;
    while r < rows
        invariant r <= rows
        invariant result.len() == r * cols
        invariant forall|i: nat, j: nat| i < r && j < cols ==> result[i * cols + j] == mat[i][j]
        decreases rows - r
    {
        let mut c: nat = 0;
        while c < cols
            invariant c <= cols
            invariant result.len() == r * cols + c
            invariant forall|i: nat, j: nat| i < r && j < cols ==> result[i * cols + j] == mat[i][j]
            invariant forall|j: nat| j < c ==> result[r * cols + j] == mat[r][j]
            decreases cols - c
        {
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