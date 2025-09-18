// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_flip(m: Vec<f32>) -> (result: Vec<f32>)
    ensures 
        result.len() == m.len(),
        forall|i: int| 0 <= i < m.len() ==> result[i] == m[m.len() - 1 - i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed the loop invariant to correctly reflect the reversed indexing */
    let mut result = Vec::new();
    for i in 0..m.len()
        invariant
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == m@[m@.len() - 1 - j]
    {
        result.push(m[m.len() - 1 - i]);
    }
    result
}
// </vc-code>

}
fn main() {}