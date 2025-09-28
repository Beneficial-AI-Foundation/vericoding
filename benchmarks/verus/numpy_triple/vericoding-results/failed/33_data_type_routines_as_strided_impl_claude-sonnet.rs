// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): bounds checking predicate */
fn valid_strided_index(i: usize, stride: usize, x_len: usize) -> bool
{
    i * stride < x_len
}
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
    /* code modified by LLM (iteration 5): added bounds checks and cast handling */
    let mut result = Vec::new();
    let mut i = 0;
    while i < m
        invariant
            i <= m,
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] == x@[j * stride as int],
        decreases m - i
    {
        assert(i < m);
        assert(i * stride < x@.len()) by {
            assert(m * stride <= x@.len());
            assert(i < m);
        };
        let idx = i * stride;
        result.push(x[idx]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}