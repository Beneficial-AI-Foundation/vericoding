// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn fmin(x: Vec<f32>, y: Vec<f32>) -> (result: Vec<f32>)
    requires x.len() == y.len(),
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> #[trigger] result[i] == x[i] || #[trigger] result[i] == y[i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Added precondition to loop invariant. */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            x.len() == y.len(),
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result.view().index(j) == x.view().index(j) || #[trigger] result.view().index(j) == y.view().index(j),
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