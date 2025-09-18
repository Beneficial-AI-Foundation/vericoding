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
    /* code modified by LLM (iteration 2): fixed compilation error by using unsafe indexing for verified exec Vec access */
    let mut result: Vec<f32> = Vec::with_capacity(m);
    for i in 0..m {
        proof {
            assert(i * stride < m * stride <= x.len());
        }
        unsafe { result.push((*x)[i * stride as usize]); }
    }
    result
}
// </vc-code>

}
fn main() {}