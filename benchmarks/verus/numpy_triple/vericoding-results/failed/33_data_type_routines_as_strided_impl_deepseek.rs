// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): cast i to nat for proper type usage */
proof fn index_lemma(x: &Vec<f32>, stride: usize, m: usize, i: nat)
    requires
        stride > 0,
        m * stride <= x.len(),
        i < m,
    ensures
        i * stride < x.len(),
{
    assert(i < m);
    assert((i as usize) * stride <= (m - 1) * stride);
    assert((m - 1) * stride < m * stride);
    assert(m * stride <= x.len());
}
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
/* code modified by LLM (iteration 5): use nat type for index_lemma parameter to avoid int cast error */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant
            i <= m,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == x@[j * stride],
        decreases m - i,
    {
        index_lemma(x, stride, m, i as nat);
        assert(i * stride < x.len());
        result.push(x[i * stride]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}