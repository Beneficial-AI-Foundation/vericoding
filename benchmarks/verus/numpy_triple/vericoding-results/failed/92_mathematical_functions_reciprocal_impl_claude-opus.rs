// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_reciprocal(x: Vec<f32>) -> (result: Vec<f32>)
    requires 
        x.len() > 0,
        forall|i: int| 0 <= i < x.len() ==> x[i] != 0.0_f32,
    ensures
        result.len() == x.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added precondition checking to ensure x[i] is non-zero before division */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == 1.0_f32 / x[j],
        decreases x.len() - i
    {
        proof {
            assert(0 <= i as int);
            assert((i as int) < x.len());
            assert(forall|k: int| 0 <= k < x.len() ==> x[k] != 0.0_f32);
            assert(x[i as int] != 0.0_f32);
        }
        let val = x[i];
        let recip = 1.0_f32 / val;
        result.push(recip);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}