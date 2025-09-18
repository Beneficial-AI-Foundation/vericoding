// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helper needed, leaving empty. */
// </vc-helpers>

// <vc-spec>
fn numpy_as_strided(x: &Vec<f32>, stride: usize, m: usize) -> (result: Vec<f32>)
    requires 
        stride > 0,
        m * stride <= x.len(),
    ensures
        result.len() == m,
        forall|i: int| 0 <= i < m ==> result[i] == x[i * stride],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed integer type casting in array access to resolve compilation error and added necessary conditions for indexing. */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant
            0 <= i as int && i as int <= m as int,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result.wf_idx(j) && result[j] == x@[(j * stride) as int],
            (i * stride) <= x.len(), // ensure future access is within bounds
        decreases m - i,
    {
        // We need to ensure that the index (i * stride) is valid for x.
        // The loop invariant m * stride <= x.len() and i < m implies (i * stride) < m * stride <= x.len().
        // The index is also non-negative since i and stride are usize.
        let idx: usize = i * stride;
        result.push(x.index(idx));
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}