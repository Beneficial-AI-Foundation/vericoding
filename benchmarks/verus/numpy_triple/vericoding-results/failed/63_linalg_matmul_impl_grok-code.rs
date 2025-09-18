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
/* code modified by LLM (iteration 5): Changed while loops to loop {} with invariants inside, added decreases to all loops to ensure termination and fix compilation syntax */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    loop {
        if i >= A.len() {
            break;
        }
        invariant result.len() == i as int;
        decreases (A.len() - i) as int;
        let mut row = Vec::new();
        let mut j: usize = 0;
        loop {
            if j >= B[0].len() {
                break;
            }
            invariant row.len() == j as int;
            decreases (B[0].len() - j) as int;
            let mut sum = 0.0f32;
            let mut k: usize = 0;
            loop {
                if k >= B.len() {
                    break;
                }
                decreases B.len() - k as int;
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