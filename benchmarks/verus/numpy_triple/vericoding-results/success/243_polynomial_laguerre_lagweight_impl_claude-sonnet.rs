// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn lagweight(x: Vec<f32>) -> (result: Vec<f32>)
    ensures result.len() == x.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to fix verification error */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            result.len() == i,
            i <= x.len(),
        decreases x.len() - i
    {
        result.push(x[i]);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}