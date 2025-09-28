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
        forall|i: int| 0 <= i < x@.len() ==> x@[i] != 0.0f32,
    ensures
        result@.len() == x@.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type mismatch by casting usize to int for indexing in assert */
    let mut result: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= (i as int) <= x@.len(),
            result@.len() == (i as int),
        decreases x.len() - i
    {
        assert(x@[i as int] != 0.0f32);
        result.push(1.0f32 / x[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}