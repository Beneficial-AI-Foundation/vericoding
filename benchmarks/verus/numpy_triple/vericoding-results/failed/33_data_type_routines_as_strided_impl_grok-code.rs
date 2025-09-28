// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_as_strided(x: &Vec<f32>, stride: usize, m: usize) -> (result: Vec<f32>)
    requires 
        stride > 0,
        m * stride <= x@.len(),
    ensures
        result@.len() == m,
        forall|i: int| 0 <= i < m ==> result@[i] == x@[i * stride as int],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Implemented loop to construct strided array with invariants for verification */
    let mut result = Vec::new();
    let mut i = 0;
    while i < m
        invariant
            result@.len() == i as int,
            forall |j: int| 0 <= j < i ==> result@[j] == x@[j * stride as int],
        decreases m as int - i as int
    {
        assert((i as int) * (stride as int) < x@.len());
        result.push(x[i * stride]);
        i += 1;
    }
    proof {
        assert forall |k: int| 0 <= k < m ==> k * stride as int < x@.len();
    }
    result
}
// </vc-code>

}
fn main() {}