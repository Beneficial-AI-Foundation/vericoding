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
{
    /* code modified by LLM (iteration 5): removed proof block and fixed assertion placement */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            i <= x1.len(),
            result.len() == i,
            x1.len() == x2.len(),
            forall|j: int| 0 <= j < x2.len() ==> x2@[j] != 0.0,
        decreases x1.len() - i
    {
        assert(i < x2.len());
        assert(x2@[i as int] != 0.0);
        result.push(x1[i] / x2[i]);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}