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
    /* code modified by LLM (iteration 3): Removed result.capacity() == x.len() from invariant as capacity is not directly observable. */
    let mut result: Vec<f32> = Vec::new();
    result.reserve(x.len());
    let mut i: usize = 0;

    while i < x.len()
        invariant
            0 <= i && i <= x.len(),
            result.len() == i,
            x.len() == y.len(),
            forall|j: int| 0 <= j < i ==> result@[j] == x@[j] || result@[j] == y@[j]
        decreases x.len() - i
    {
        if x[i] < y[i] {
            result.push(x[i]);
        } else {
            result.push(y[i]);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}