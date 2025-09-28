// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): No helper functions needed at this stage, so this section is empty. */
// </vc-helpers>

// <vc-spec>
fn numpy_flat(a: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed the invariant syntax by making each condition a separate boolean expression joined by `&&` for the `while` loop. */
{
    let mut result: Vec<f32> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant (
            result.len() == i
            && (
                forall|j: int| 0 <= j < i ==> result[j] == a[j]
            )
            && i <= a.len()
        )
        decreases a.len() - i
    {
        result.push(a[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}