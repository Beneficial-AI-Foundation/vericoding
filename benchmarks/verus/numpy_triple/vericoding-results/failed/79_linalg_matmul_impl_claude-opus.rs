// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn matmul(A: Vec<Vec<i8>>, B: Vec<Vec<i8>>) -> (result: Vec<Vec<i8>>)
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
    /* code modified by LLM (iteration 3): Added decreases clauses to all loops */
    let m = A.len();
    let n = B[0].len();
    let p = B.len();
    
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0;
    
    while i < m
        invariant
            i <= m,
            result.len() == i,
            m == A.len(),
            n == B@[0].len(),
            p == B.len(),
            p == A@[0].len(),
            forall|k: int| 0 <= k < i ==> #[trigger] result@[k].len() == n,
            forall|k: int| 0 <= k < A.len() ==> #[trigger] A@[k].len() == p,
            forall|k: int| 0 <= k < B.len() ==> #[trigger] B@[k].len() == n,
        decreases m - i
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j: usize = 0;
        
        while j < n
            invariant
                j <= n,
                row.len() == j,
                n == B@[0].len(),
                p == B.len(),
                p == A@[0].len(),
                i < m,
                forall|k: int| 0 <= k < A.len() ==> #[trigger] A@[k].len() == p,
                forall|k: int| 0 <= k < B.len() ==> #[trigger] B@[k].len() == n,
            decreases n - j
        {
            let mut sum: i8 = 0;
            let mut k: usize = 0;
            
            while k < p
                invariant
                    k <= p,
                    p == B.len(),
                    p == A@[0].len(),
                    i < m,
                    j < n,
                    forall|l: int| 0 <= l < A.len() ==> #[trigger] A@[l].len() == p,
                    forall|l: int| 0 <= l < B.len() ==> #[trigger] B@[l].len() == n,
                decreases p - k
            {
                sum = sum + A[i][k] * B[k][j];
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