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
    /* code modified by LLM (iteration 5): added bounds checking and arithmetic overflow prevention */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant
            i <= m,
            result@.len() == i as int,
            forall|j: int| 0 <= j < i ==> 0 <= j * stride as int < x@.len(),
            forall|j: int| 0 <= j < i ==> result@[j] == x@[j * stride as int],
            m * stride <= x@.len(),
            stride > 0,
        decreases m - i
    {
        assert(i < m);
        assert(m * stride <= x@.len());
        assert(i * stride < m * stride);
        assert(i * stride < x@.len());
        result.push(x[i * stride]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}