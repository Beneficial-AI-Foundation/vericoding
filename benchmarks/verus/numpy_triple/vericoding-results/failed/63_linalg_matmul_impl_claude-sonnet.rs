// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added proper index bounds checking */
exec fn dot_product_exec(row: &Vec<f32>, col: &Vec<f32>) -> (result: f32)
    requires row.len() == col.len()
{
    let mut sum = 0.0;
    let len = row.len();
    for i in 0..len
        invariant
            i <= len,
            len == row.len(),
            len == col.len(),
            i <= row.len(),
            i <= col.len()
    {
        sum = sum + row[i] * col[i];
    }
    sum
}
// </vc-helpers>

// <vc-spec>
fn matmul(A: Vec<Vec<f32>>, B: Vec<Vec<f32>>) -> (result: Vec<Vec<f32>>)
    requires
        A.len() > 0,
        B.len() > 0,
        A@[0].len() == B.len(),
        forall|i: int| 0 <= i < A.len() ==> #[trigger] A@[i].len() == A@[0].len(),
        forall|i: int| 0 <= i < B.len() ==> #[trigger] B@[i].len() == B@[0].len(),
    ensures
        result.len() == A.len(),
        result.len() > 0 ==> result@[0].len() == B@[0].len(),
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result@[i].len() == B@[0].len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed invariants and bounds checking */
    let mut result: Vec<Vec<f32>> = Vec::new();
    let rows = A.len();
    let cols = B[0].len();
    let inner_dim = A[0].len();
    
    for i in 0..rows
        invariant
            result.len() == i,
            i <= rows,
            rows == A.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] result@[k].len() == cols
    {
        let mut row: Vec<f32> = Vec::new();
        for j in 0..cols
            invariant
                row.len() == j,
                j <= cols,
                result.len() == i,
                i < A.len(),
                forall|k: int| 0 <= k < i ==> #[trigger] result@[k].len() == cols
        {
            let mut sum = 0.0;
            for k in 0..inner_dim
                invariant
                    row.len() == j,
                    result.len() == i,
                    k <= inner_dim,
                    i < A.len(),
                    inner_dim == A[0].len(),
                    inner_dim == B.len(),
                    j < cols,
                    cols == B[0].len(),
                    k <= A[i].len(),
                    forall|l: int| 0 <= l < A.len() ==> #[trigger] A@[l].len() == inner_dim,
                    forall|l: int| 0 <= l < B.len() ==> #[trigger] B@[l].len() == cols
            {
                sum = sum + A[i][k] * B[k][j];
            }
            row.push(sum);
        }
        result.push(row);
    }
    result
}
// </vc-code>

}
fn main() {}