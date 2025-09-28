// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): create zero-initialized vector of f32 */
fn zeros_f32(n: usize) -> Vec<f32>
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < result@.len() ==> result@[i] == 0.0f32,
{
    let mut res: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            res.len() == i,
            forall|j: int| 0 <= j < res@.len() ==> res@[j] == 0.0f32,
        decreases n - i,
    {
        res.push(0.0f32);
        i = i + 1;
    }
    res
}

// </vc-helpers>

// <vc-spec>
fn diag(v: Vec<f32>) -> (result: Vec<Vec<f32>>)
    requires v.len() > 0,
    ensures 
        result.len() == v.len(),
        forall|i: int| 0 <= i < v@.len() ==> result@[i].len() == v@.len(),
        /* Elements on the main diagonal are from v */
        forall|i: int| 0 <= i < v@.len() ==> result@[i][i] == v@[i],
        /* All off-diagonal elements are zero */
        forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() && i != j ==> result@[i][j] == 0.0f32,
        /* Diagonal matrix property - non-zero elements only on diagonal */
        forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() && result@[i][j] != 0.0f32 ==> i == j,
        /* The resulting matrix is symmetric */
        forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() ==> result@[i][j] == result@[j][i],
        /* Each row has exactly one non-zero element at position i (unless v[i] = 0) */
        forall|i: int| 0 <= i < v@.len() && v@[i] != 0.0f32 ==> {
            result@[i][i] != 0.0f32 && 
            forall|j: int| 0 <= j < v@.len() && j != i ==> result@[i][j] == 0.0f32
        },
        /* Each column has exactly one non-zero element at position j (unless v[j] = 0) */
        forall|j: int| 0 <= j < v@.len() && v@[j] != 0.0f32 ==> {
            result@[j][j] != 0.0f32 && 
            forall|i: int| 0 <= i < v@.len() && i != j ==> result@[i][j] == 0.0f32
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build diagonal matrix avoiding spec-only int/nat in executable code */
    let n: usize = v.len();
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == i,
            forall|k: int| 0 <= k < result@.len() ==> result@[k].len() == v@.len(),
            forall|k: int| 0 <= k < result@.len() ==> forall|j: int| 0 <= j < v@.len() ==> result@[k][j] == (if k == j { v@[k] } else { 0.0f32 }),
        decreases n - i,
    {
        let mut row: Vec<f32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                row.len() == j,
                forall|t: int| 0 <= t < row@.len() ==> row@[t] == (if t == i as int { v@[t] } else { 0.0f32 }),
            decreases n - j,
        {
            if j == i {
                row.push(v[j]);
            } else {
                row.push(0.0f32);
            }
            j = j + 1;
        }
        result.push(row);
        i = i + 1;
    }
    result
}

// </vc-code>


}
fn main() {}