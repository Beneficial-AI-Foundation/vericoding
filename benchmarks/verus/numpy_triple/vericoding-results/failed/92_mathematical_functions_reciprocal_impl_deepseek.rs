// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed parameter type to use int instead of usize for spec compatibility */
fn numpy_reciprocal_helper(x: Vec<f32>, i: int) -> (result: f32)
    requires
        0 <= i < x.len(),
        x[i] != 0.0_f32,
    ensures
        result == 1.0_f32 / x[i]
{
    1.0_f32 / x[i]
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
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i >= 0,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == 1.0_f32 / x[j],
        decreases x.len() - i
    {
        let element = numpy_reciprocal_helper(x.clone(), i as int);
        result.push(element);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}