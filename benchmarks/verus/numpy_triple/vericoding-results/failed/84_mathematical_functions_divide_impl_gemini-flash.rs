// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Adding & to ensure x2 is a reference for well_defined_division. */
spec fn well_defined_division(x2: &Vec<f32>) -> bool {
    forall|i: int| #![auto] 0 <= i && i < x2.len() ==> x2@.index(i) != 0.0f32
}
// </vc-helpers>

// <vc-spec>
fn numpy_divide(x1: Vec<f32>, x2: Vec<f32>) -> (result: Vec<f32>)
    requires 
        x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < x1.len() ==> x2[i] != 0.0f32,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed errors by using `.index()` for Seq access and `result.insert` instead of `result.push`. */
{
    let mut result: Vec<f32> = Vec::new();
    result.reserve(x1.len());
    let mut i: usize = 0;
    while i < x1.len()
        invariant (
            0 <= i && i <= x1.len(),
            result.len() == i,
            x1.len() == x2.len(),
            well_defined_division(&x2),
        )
    {
        result.insert(i, x1@.index(i) / x2@.index(i));
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}