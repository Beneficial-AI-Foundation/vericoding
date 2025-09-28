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
/* code modified by LLM (iteration 5): removed assume statements; used truncate for sum cast to i8 */
    let mut result = Vec::new();
    let a_rows = A.len();
    let b_rows = B.len();
    let b_cols = B[0].len();
    proof {
        assert(a_rows > 0);
        assert(b_rows > 0);
        assert(A@[0].len() == b_rows);
        assert(forall|i: int| 0 <= i < a_rows ==> #[trigger] A@[i].len() == b_rows);
        assert(forall|i: int| 0 <= i < b_rows ==> #[trigger] B@[i].len() == b_cols);
    }
    for i in 0..a_rows {
        proof { assert((i as int) < A@.len()); }
        let mut row = Vec::new();
        for j in 0..b_cols {
            proof { assert(j < b_cols); }
            let mut sum: i32 = 0;
            for k in 0..b_rows {
                proof {
                    assert((i as int) < A@.len());
                    assert(k < b_rows);
                    assert((k as int) < B@.len());
                    assert(j < B@[k as int].len());
                }
                let term = (A[i][k] as i32) * (B[k][j] as i32);
                sum = sum + term;
            }
            row.push(#[verifier::truncate] sum as i8);
        }
        result.push(row);
    }
    result
}
// </vc-code>

}
fn main() {}