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
    /* code modified by LLM (iteration 3): added assertions to ensure index bounds for vector access */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            i <= x1.len(),
            result.len() == i,
        decreases x1.len() - i
    {
        proof {
            assert(i < x1.len());
        }
        result.push(x1[i] / x2[i]);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}