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
    /* code modified by LLM (iteration 5): added proof block to establish precondition for x[i][i] access */
    let n = x.len();
    let mut sum: f32 = 0.0;
    let mut i: usize = 0;
    
    while i < n
        invariant
            i <= n,
            n == x@.len(),
            forall|j: int| 0 <= j < n ==> x@[j].len() == n,
        decreases n - i
    {
        proof {
            assert(0 <= i < n);
            assert(x@[i as int].len() == n);
            assert(i < x@[i as int].len());
        }
        sum = sum + x[i][i];
        i = i + 1;
    }
    
    sum
}
// </vc-code>


}
fn main() {}