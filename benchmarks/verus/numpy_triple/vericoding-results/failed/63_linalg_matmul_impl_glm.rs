// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added helper to check matrix dimensions */
spec fn valid_matrix_dimensions<T>(matrix: Vec<Vec<T>>, rows: int, cols: int) -> bool {
    matrix.len() == rows && (rows > 0 ==> matrix@[0].len() == cols)
}

/* helper modified by LLM (iteration 5): Added spec function for matrix multiplication */
spec fn matmul_spec(A: Vec<Vec<f32>>, B: Vec<Vec<f32>>, i: int, j: int, n: int) -> f32 {
    if n == 0 {
        0.0
    } else {
        matmul_spec(A, B, i, j, n - 1) + A@[i]@[n - 1] * B@[n - 1]@[j]
    }
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
/* code modified by LLM (iteration 5): Fixed array bounds checking and added proper invariants */
{
    let m = A.len();
    let n = A[0].len();
    let p = B[0].len();
    let mut result: Vec<Vec<f32>> = Vec::with_capacity(m);
    
    for i in 0..m
        invariant
            0 <= i <= m,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] result@[k].len() == p,
            forall|k: int| 0 <= k < i ==> forall|l: int| 0 <= l < p ==> result@[k]@[l] == matmul_spec(A, B, k, l, n),
    {
        let mut row: Vec<f32> = Vec::with_capacity(p);
        
        for j in 0..p
            invariant
                0 <= j <= p,
                row.len() == j,
                forall|l: int| 0 <= l < j ==> row@[l] == matmul_spec(A, B, i, l, n),
        {
            let mut acc = 0.0;
            
            for k in 0..n
                invariant
                    0 <= k <= n,
                    acc == matmul_spec(A, B, i, j, k),
                {
                assert(i < A.len() && k < A[i].len());
                assert(k < B.len() && j < B[k].len());
                acc = acc + A[i][k] * B[k][j];
                }
            
            row.push(acc);
            assert(row.len() == j + 1);
        }
        
        result.push(row);
        assert(result.len() == i + 1);
    }
    
    result
}
// </vc-code>

}
fn main() {}