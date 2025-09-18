// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added proof body to lemma_stride_bound using non-linear arithmetic. */
proof fn lemma_stride_bound(i: nat, m: nat, stride: nat, len: nat)
    requires
        i < m,
        stride > 0,
        m * stride <= len,
    ensures
        i * stride < len,
{
    vstd::arithmetic::mul_le_mono(i + 1, m, stride);
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
/* code modified by LLM (iteration 5): Added invariants to carry preconditions and prove index safety. */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant
            i <= m,
            stride > 0,
            m * stride <= x.len(),
            result.len() == i,
            forall|j: nat| j < i ==> (j * stride) < x.len(),
            forall|j: nat| j < i ==> result@[j] == x@[j * stride],
        decreases m - i,
    {
        lemma_stride_bound(i as nat, m as nat, stride as nat, x.len() as nat);
        
        let val = x[i * stride];
        result.push(val);
        i = i + 1;

        proof {
            assert forall|j: nat| j < i implies (j * stride) < x.len() by {
                lemma_stride_bound(j, m as nat, stride as nat, x.len() as nat);
            }
        }
    }
    result
}
// </vc-code>

}
fn main() {}