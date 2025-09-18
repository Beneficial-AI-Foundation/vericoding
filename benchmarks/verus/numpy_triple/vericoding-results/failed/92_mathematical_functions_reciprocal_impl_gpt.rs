// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): reciprocal with explicit non-zero precondition */
fn reciprocal(x: f32) -> f32
    requires
        x != 0.0_f32
{
    1.0_f32 / x
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
    /* code modified by LLM (iteration 5): prove non-zero elements before division and build result vector */
    let mut result: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i
        decreases x.len() - i
    {
        proof {
            let ii: int = i as int;
            assert(0 <= ii);
            assert(ii < x.len() as int);
            assert(x[i] != 0.0_f32);
        }
        let ri = reciprocal(x[i]);
        result.push(ri);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}