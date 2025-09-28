// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed. */
// </vc-helpers>

// <vc-spec>
fn logical_not(x: Vec<f64>) -> (result: Vec<bool>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x[i] == 0.0)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed loop invariant to account for result.len() being the current value of i before the push, not after. */
{
    let mut result: Vec<bool> = Vec::with_capacity(x.len());
    let mut i: usize = 0;

    while i < x.len()
        invariant 
            0 <= i as int && i as int <= x.len() as int,
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result@[j] == (x@[j] == 0.0),
        decreases x.len() - i
    {
        result.push(x[i] == 0.0);
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}