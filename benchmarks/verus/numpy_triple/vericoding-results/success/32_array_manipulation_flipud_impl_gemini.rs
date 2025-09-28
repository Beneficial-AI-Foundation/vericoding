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
    let mut result: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < m.len()
        invariant
            i <= m.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == m@[(m.len() as int) - 1 - j],
        decreases m.len() - i
    {
        let index = m.len() - 1 - i;
        result.push(m[index]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}