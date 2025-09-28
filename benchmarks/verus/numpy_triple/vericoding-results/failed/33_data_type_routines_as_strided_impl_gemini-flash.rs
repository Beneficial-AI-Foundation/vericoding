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
{ /* code modified by LLM (iteration 5): [cast `i` to `usize` for indexing `x`] */
    let mut result_vec = Vec::new();
    let mut i = 0;
    while i < m
        invariant
            i <= m,
            result_vec@.len() == i,
            forall|k: int| 0 <= k < i ==> result_vec@[k] == x@[k * stride as int],
            m * stride <= x@.len()
        decreases m - i
    {
        result_vec.push(x[i * stride as usize]); // Fix: Cast `i` to `usize` for array indexing.
        i = i + 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}