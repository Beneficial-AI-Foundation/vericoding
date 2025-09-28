// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn reshape(a: Vec<f32>) -> (result: Vec<f32>)
    requires a.len() > 0,
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Added decreases clause (a.len() - i) as nat to the while loop */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i >= 0,
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> (#[trigger] result@[j]) == a@[j],
        decreases (a.len() - i) as nat
    {
        result.push(a[i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}