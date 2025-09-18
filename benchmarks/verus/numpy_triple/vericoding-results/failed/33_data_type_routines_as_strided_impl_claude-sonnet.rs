// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added bounds checking helper for safe array access */
spec fn valid_strided_access(x_len: int, i: int, stride: int, m: int) -> bool {
    0 <= i < m && stride > 0 && i * stride < x_len
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
{
    /* code modified by LLM (iteration 5): fixed assertion by using correct type casts */
    let mut result: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] == x@[j * (stride as int)],
            i <= m,
            stride > 0,
            m * stride <= x.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] (j * (stride as int)) < x.len()
        decreases m - i
    {
        proof {
            assert(i < m);
            assert((i as int) * (stride as int) < (m as int) * (stride as int));
            assert((m as int) * (stride as int) <= x.len());
            assert((i as int) * (stride as int) < x.len());
        }
        result.push(x[i * stride]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}