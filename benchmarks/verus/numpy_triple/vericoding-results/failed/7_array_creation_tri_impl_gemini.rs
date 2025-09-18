// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn tri(n: usize, m: usize, k: i32) -> (result: Vec<Vec<f64>>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i].len() == m,
        forall|i: int, j: int| 0 <= i < n && 0 <= j < m ==> 
            result[i][j] == if j <= i + k { 1.0 } else { 0.0 }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Replaced ghost type `int` with executable integer types and logic to avoid overflow/underflow. */
    Vec::new_with_len(n, |i: usize| -> Vec<f64> {
        Vec::new_with_len(m, |j: usize| -> f64 {
            let condition = if k >= 0 {
                let k_pos = k as usize;
                j <= i || (j - i) <= k_pos
            } else {
                let k_neg = (-(k as i64)) as usize;
                i >= j && k_neg <= (i - j)
            };

            if condition { 1.0 } else { 0.0 }
        })
    })
}
// </vc-code>

}
fn main() {}