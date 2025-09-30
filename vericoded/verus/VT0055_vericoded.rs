// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn flipud(m: Vec<f32>) -> (result: Vec<f32>)
    ensures 
        result.len() == m.len(),
        forall|i: int| 0 <= i < m.len() ==> result[i] == m[m.len() - 1 - i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to while loop */
    let mut result = Vec::new();
    let mut i = 0;
    while i < m.len()
        invariant
            i <= m.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == m[m.len() - 1 - j],
        decreases m.len() - i
    {
        result.push(m[m.len() - 1 - i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}