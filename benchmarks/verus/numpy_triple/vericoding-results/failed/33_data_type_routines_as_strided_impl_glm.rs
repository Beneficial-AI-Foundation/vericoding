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
    let mut result = Vec::new();
    let mut i = 0;
    while i < m
        invariant
            0 <= i <= m,
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == x@[j * (stride as int)],
        decreases m - i,
    {
        result.push(x[i * stride]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}