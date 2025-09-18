// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add helper function to verify non-zero property for indexing */
proof fn x_non_zero_at_index(x: &Vec<f32>, i: usize)
    requires
        0 <= i < x.len(),
        forall|j: int| 0 <= j < x.len() ==> x[j] != 0.0_f32,
    ensures
        x[i] != 0.0_f32
{
    assert(0 <= i < x.len());
    assert(x[i] != 0.0_f32);
}
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
    /* code modified by LLM (iteration 5): add proof to establish precondition for division */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
        decreases x.len() - i
    {
        proof {
            x_non_zero_at_index(&x, i);
        }
        result.push(1.0_f32 / x[i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}