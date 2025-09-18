// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn logical_not(x: Vec<f64>) -> (result: Vec<bool>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x[i] == 0.0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added loop invariant with @ access to prove postcondition */
    let len = x.len();
    let mut result: Vec<bool> = Vec::new();
    for i in 0..len
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == (x@[j] == 0.0)
        {
        result.push(x@[i] == 0.0);
    }
    result
}
// </vc-code>

}
fn main() {}