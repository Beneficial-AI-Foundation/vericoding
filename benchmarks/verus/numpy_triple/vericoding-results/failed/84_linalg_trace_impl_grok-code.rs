// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
/* code modified by LLM (iteration 5): Fixed type mismatch by using int for loop indices and casting to usize for array access to resolve compilation error. */
    let length = x@.len();
    proof {
        // n is x@.len() which is int
    }
    let mut sum = 0.0f32;
    let mut i = 0;
    while i < length
        invariant
            0 <= i <= length,
            (exists|k: int| 0 <= k < i ==> x@[k][k] != 0.0f32) ==> sum != 0.0f32
        decreases length - i
    {
        proof {
            assert(i < x@.len());
            assert(x@[i].len() == x@.len());
        }
        sum = sum + x[i as usize][i as usize];
        i += 1;
    }
    sum
}
// </vc-code>


}
fn main() {}