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
    /* code modified by LLM (iteration 5): fixed compilation error by casting arguments to int instead of nat for the lemma call */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant
            stride > 0,
            m * stride <= x@.len(),
            0 <= i <= m,
            result@.len() == i as nat,
            forall|j: int| 0 <= j < i ==> result@[j] == x@[j * stride as int],
        decreases m - i
    {
        proof {
            vstd::arithmetic::mul::lemma_mul_strict_inequality(i as int, m as int, stride as int);
        }
        let val = x[i * stride];
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}