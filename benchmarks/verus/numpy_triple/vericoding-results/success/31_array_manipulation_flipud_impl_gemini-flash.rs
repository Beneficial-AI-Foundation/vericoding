// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): removed as it's not a helper and was empty */
// </vc-helpers>

// <vc-spec>
fn flipud(m: Vec<f32>) -> (result: Vec<f32>)
    ensures 
        result.len() == m.len(),
        forall|i: int| 0 <= i < m.len() ==> result[i] == m[m.len() - 1 - i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): added decreases clause to the loop */
{
    let mut result = Vec::new();

    let mut i = 0;
    while i < m.len()
        invariant
            0 <= i <= m.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == m@[m.len() - 1 - j],
        decreases m.len() - i
    {
        let idx = m.len() - 1 - i;
        result.push(m[idx as usize]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}