// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn pos_implies_nonneg(s: int)
    requires
        0 < s,
    ensures
        0 <= s,
{
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
    let mut result: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant
            stride > 0,
            m * stride <= x@.len(),
            0 <= i <= m,
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == x@[j * stride as int],
        decreases m - i
    {
        let idx: usize = i * stride;
        proof {
            assert(x@.len() == x.len() as int);
            let i_i: int = i as int;
            let m_i: int = m as int;
            let s_i: int = stride as int;
            assert(i_i < m_i);
            assert(0 < s_i);
            assert(i_i + 1 <= m_i);
            assert((i_i + 1) * s_i <= m_i * s_i);
            assert(m_i * s_i <= x@.len());
            assert(i_i * s_i + s_i == (i_i + 1) * s_i);
            assert(i_i * s_i < (i_i + 1) * s_i);
            assert((idx as int) == i_i * s_i);
            assert((idx as int) < x@.len());
            assert((idx as int) < x.len() as int);
        }
        let v = x[idx];
        result.push(v);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}