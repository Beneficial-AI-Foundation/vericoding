// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

fn diagonal_sum(x: Vec<Vec<f32>>, i: int) -> (sum: f32)
    requires
        0 <= i <= x@.len(),
        forall|k: int| 0 <= k < x@.len() ==> x@[k].len() == x@.len(),
    ensures
        i == 0 ==> sum == 0.0f32,
        i > 0 ==> sum == diagonal_sum(x, i-1) + x@[i-1][i-1],
{
    if i == 0 {
        0.0
    } else {
        let prev = diagonal_sum(x, i-1);
        prev + x@[i-1][i-1]
    }
}

/* helper modified by LLM (iteration 5): Fix seq macro syntax - use explicit lambda parameter */
proof fn diagonal_sum_properties(x: Vec<Vec<f32>>, n: nat)
    requires
        n <= x@.len(),
        forall|k: int| 0 <= k < x@.len() ==> x@[k].len() == x@.len(),
    ensures
        diagonal_sum(x, n) == seq![k: int | 0 <= k < n].map(|k: int| x@[k][k]).sum(),
    decreases n,
{
    if n > 0 {
        diagonal_sum_properties(x, n-1);
    }
}

// </vc-helpers>

// <vc-spec>
fn trace(x: Vec<Vec<f32>>) -> (result: f32)
    requires 
        x@.len() > 0,
        forall|i: int| 0 <= i < x@.len() ==> x@[i].len() == x@.len(),
    ensures 
        true, /* The trace equals the sum of diagonal elements matrix[i][i] for i in 0..n-1 */
        forall|i: int| 0 <= i < x@.len() ==> x@[i][i] != 0.0f32 ==> result != 0.0f32,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Use corrected seq macro syntax with explicit lambda */
    let n = x.len();
    proof {
        diagonal_sum_properties(x, n);
    }
    let sum = diagonal_sum(x, n);
    sum
}
// </vc-code>


}
fn main() {}