// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn true_divide(x1: Vec<f64>, x2: Vec<f64>) -> (result: Vec<f64>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x2.len() ==> x2@[i] != 0.0,
    ensures
        result.len() == x1.len(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected type casting for indexing, using `i` directly for `nat` indexing. */
{
    let len = x1.len();
    let mut result = Vec::with_capacity(len);
    let mut i: nat = 0;

    while i < len
        invariant
            0 <= i,
            i <= len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == x1@[j] / x2@[j],
        decreases len - i
    {
        // Casting `i` to `int` for indexing into `x1` and `x2` is only needed when used in ghost contexts.
        // Since x1 and x2 are `Vec<f64>`, they use concrete indexing. `i` is a `nat` which can be used directly for indexing.
        let val = x1@[(i as usize)] / x2@[(i as usize)];
        result.push(val);
        i = i + 1;
    }

    result
}
// </vc-code>


}
fn main() {}