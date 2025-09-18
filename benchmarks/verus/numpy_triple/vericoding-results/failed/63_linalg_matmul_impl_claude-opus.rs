// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Fixed array access bounds by adding proper invariants */
    let m = A.len();
    let n = B[0].len();
    let p = B.len();
    
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    
    while i < m
        invariant
            i <= m,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] result@[k].len() == n,
            m == A.len(),
            n == B@[0].len(),
            p == B.len(),
            p > 0,
            B.len() > 0,
            A@[0].len() == p,
            forall|k: int| 0 <= k < A.len() ==> #[trigger] A@[k].len() == p,
            forall|k: int| 0 <= k < B.len() ==> #[trigger] B@[k].len() == n,
        decreases m - i
    {
        let mut row: Vec<f32> = Vec::new();
        let mut j: usize = 0;
        
        while j < n
            invariant
                j <= n,
                row.len() == j,
                i < m,
                m == A.len(),
                n == B@[0].len(),
                p == B.len(),
                p > 0,
                B.len() > 0,
                A@[0].len() == p,
                forall|k: int| 0 <= k < A.len() ==> #[trigger] A@[k].len() == p,
                forall|k: int| 0 <= k < B.len() ==> #[trigger] B@[k].len() == n,
            decreases n - j
        {
            let mut sum: f32 = 0.0;
            let mut k: usize = 0;
            
            while k < p
                invariant
                    k <= p,
                    i < m,
                    j < n,
                    m == A.len(),
                    n == B@[0].len(),
                    p == B.len(),
                    p > 0,
                    B.len() > 0,
                    A@[0].len() == p,
                    i < A.len(),
                    A@[i].len() == p,
                    forall|l: int| 0 <= l < A.len() ==> #[trigger] A@[l].len() == p,
                    forall|l: int| 0 <= l < B.len() ==> #[trigger] B@[l].len() == n,
                decreases p - k
            {
                if k < p {
                    sum = sum + A[i][k] * B[k][j];
                }
                k = k + 1;
            }
            
            row.push(sum);
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