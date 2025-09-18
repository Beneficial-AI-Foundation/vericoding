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
    /* code modified by LLM (iteration 5): implemented a backward loop which is logically simpler for the verifier */
    let n = m.len();
    let mut result = Vec::new();
    let mut i = n;

    while i > 0
        invariant
            n == m.len(),
            result.len() == n - i,
            forall|k: int| 0 <= k < (n - i) as int ==> result@[k] == m@[n as int - 1 - k],
        decreases i
    {
        i = i - 1;
        result.push(m[i]);
    }

    result
}
// </vc-code>

}
fn main() {}