// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Provided recursive definition for vec_sum to enable spec side calculations */
spec fn vec_sum(a: Seq<f32>) -> f32 {
    if a.len() == 0 {
        0.0f32
    } else {
        vec_sum(a.drop_last()) + a.last()
    }
}
// </vc-helpers>

// <vc-spec>
spec fn vec_sum(a: Seq<f32>) -> f32;

fn sum(a: Vec<f32>) -> (result: f32)
    ensures 
        result == vec_sum(a@),
        a.len() == 0 ==> result == 0.0f32,
        (forall|i: int| 0 <= i < a.len() ==> a[i] == 0.0f32) ==> result == 0.0f32,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Implemented the sum function using a loop with invariants and decreases clause for termination, ensuring the sum is calculated correctly */
{
    let mut sum = 0.0f32;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            sum == vec_sum(a@.take(i as int)),
            i >= 0,
            i <= a.len() as int
        decreases a.len() - i
    {
        sum = sum + a[i];
        i = i + 1;
    }
    sum
}
// </vc-code>

}
fn main() {}