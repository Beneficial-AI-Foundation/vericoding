// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add skeleton helper */
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
    /* code modified by LLM (iteration 5): add loop invariant for sum and fix decreasing clause */
    let mut sum: f32 = 0.0;
    let mut i: usize = 0;
    let n: usize = x.len();

    while i < n
        invariant
            0 <= i,
            i <= n as int,
            sum == (
                (0..i as int).fold(0.0f32, |acc: f32, k: int| acc + x@[k as usize]@[k as usize])
            ),
        decreases n - i
    {
        sum = sum + x[i][i];
        i = i + 1;
    }

    sum
}
// </vc-code>


}
fn main() {}