// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn minimum(x1: Vec<f32>, x2: Vec<f32>) -> (result: Vec<f32>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result@.len() ==> 
            (result@[i] == x1@[i] || result@[i] == x2@[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to fix loop verification */
    let mut result = Vec::new();
    let n = x1.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            x1.len() == n,
            x2.len() == n,
            forall|j: int| 0 <= j < i ==> result@[j] == x1@[j] || result@[j] == x2@[j],
        decreases n - i
    {
        if x1[i] <= x2[i] {
            result.push(x1[i]);
        } else {
            result.push(x2[i]);
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}