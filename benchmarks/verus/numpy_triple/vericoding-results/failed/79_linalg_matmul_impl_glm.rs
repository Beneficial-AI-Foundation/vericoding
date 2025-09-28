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
    /* code modified by LLM (iteration 2): fixed innermost loop invariant to include i < m and j < n */
        let m: usize = A.len();
        let n: usize = B[0].len();
        let p: usize = A[0].len();

        let mut result: Vec<Vec<i8>> = Vec::new();
        let mut i: usize = 0;
        while i < m
            invariant
                0 <= i <= m,
                result.len() == i,
                forall|r: int| 0 <= r < i as int ==> result@[r].len() == n,
            decreases (m - i) as int,
        {
            let mut row: Vec<i8> = Vec::new();
            let mut j: usize = 0;
            while j < n
                invariant
                    0 <= j <= n,
                    row.len() == j,
                decreases (n - j) as int,
            {
                let mut sum: i8 = 0;
                let mut k: usize = 0;
                while k < p
                    invariant
                        0 <= k <= p,
                        i < m,
                        j < n,
                    decreases (p - k) as int,
                {
                    sum = sum.wrapping_add(A[i][k].wrapping_mul(B[k][j]));
                    k += 1;
                }
                row.push(sum);
                j += 1;
            }
            result.push(row);
            i += 1;
        }
        result
    }
// </vc-code>

}
fn main() {}