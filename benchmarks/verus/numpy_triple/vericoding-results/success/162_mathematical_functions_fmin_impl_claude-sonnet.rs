// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn fmin(x: Vec<f32>, y: Vec<f32>) -> (result: Vec<f32>)
    requires x@.len() == y@.len(),
    ensures
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < x@.len() ==> #[trigger] result@[i] == x@[i] || #[trigger] result@[i] == y@[i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added bounds checks and fixed invariant */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            i <= x@.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == x@[j] || result@[j] == y@[j],
            x@.len() == y@.len()
        decreases x@.len() - i
    {
        let min_val = if x[i] <= y[i] { x[i] } else { y[i] };
        result.push(min_val);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}