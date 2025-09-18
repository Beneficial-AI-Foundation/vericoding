// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Convert to ghost function with proper spec */
spec fn index_matches(mat: &Vec<Vec<f32>>, result: &Vec<f32>, r: int, c: int) -> bool {
    result[r * mat[0].len() + c] == mat[r][c]
}
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
/* code modified by LLM (iteration 5): Use usize types and fix ghost/non-ghost separation */
{
    let n = mat.len();
    let m = mat[0].len();
    let mut result = Vec::with_capacity(n * m);
    let mut i: usize = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i * m,
            forall|r: int, c: int| 0 <= r < i && 0 <= c < m ==> result[r * m + c] == mat[r][c]
    {
        let mut j: usize = 0;
        while j < m
            invariant
                0 <= j <= m,
                result.len() == i * m + j,
                forall|c: int| 0 <= c < j ==> result[i * m + c] == mat[i][c]
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