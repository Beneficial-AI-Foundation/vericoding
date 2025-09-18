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
        m * stride <= x.len(),
    ensures
        result.len() == m,
        forall|i: int| 0 <= i < m ==> result[i] == x[i * stride],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed arithmetic overflow and index bounds */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant
            i <= m,
            result@.len() == i as int,
            forall|j: int| 0 <= j < i ==> result@[j] == x@[(j * stride as int) as int],
            m * stride <= x@.len(),
            stride > 0,
            i * stride <= x@.len(),
        decreases m - i,
    {
        proof {
            assert(i < m);
            assert(m * stride <= x@.len());
            assert((i as int) < (m as int));
            assert((i as int) * (stride as int) < (m as int) * (stride as int));
            assert((m as int) * (stride as int) <= x@.len() as int);
            assert((i as int) * (stride as int) < x@.len() as int);
            let idx = i * stride;
            assert(idx < x@.len());
        }
        let idx = i * stride;
        result.push(x[idx]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}