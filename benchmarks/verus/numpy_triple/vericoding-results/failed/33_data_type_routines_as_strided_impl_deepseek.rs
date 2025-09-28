// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_mul_strided_index_valid(i: int, stride: usize, m: usize, x_len: nat)
    requires
        0 <= i < m,
        stride > 0,
        m * stride <= x_len,
    ensures
        (i * (stride as int)) as nat < x_len,
        i * (stride as int) < x_len as int,
{
    assert(stride > 0);
    assert(i < m);
    assert(i * (stride as int) <= (m - 1) * (stride as int));
    assert((m - 1) * (stride as int) < m * (stride as int));
    assert(m * (stride as int) <= x_len as int);
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
    /* code modified by LLM (iteration 5): Fixed loop invariant and ensures conditions */
    let mut result = Vec::new();
    let mut j: usize = 0;
    while j < m
        invariant
            result@.len() == j,
            forall|k: int| 0 <= k < j ==> (k * (stride as int) < x@.len() as int) && result@[k] == x@[k * (stride as int)],
            j <= m,
        decreases m - j,
    {
        proof { lemma_mul_strided_index_valid(j as int, stride, m, x@.len()); }
        let index = j * stride;
        result.push(x[index]);
        j = j + 1;
    }
    result
}
// </vc-code>

}
fn main() {}