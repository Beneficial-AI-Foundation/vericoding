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
    /* code modified by LLM (iteration 3): strengthened invariant and added bounds assertions */
    let mut result = Vec::with_capacity(x1.len());
    let mut i = 0;
    while i < x1.len()
        invariant
            x1.len() == x2.len(),
            i <= x1.len(),
            i <= x2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> (result@[j] == x1@[j] || result@[j] == x2@[j]),
        decreases x1.len() - i
    {
        assert(i < x1.len());
        assert(i < x2.len());
        let m = if x1[i] <= x2[i] { x1[i] } else { x2[i] };
        result.push(m);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}