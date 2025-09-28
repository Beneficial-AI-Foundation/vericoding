// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn polynomial(coef: Vec<f64>, domain: Vec<f64>, window: Vec<f64>) -> (result: Vec<f64>)
    requires 
        domain.len() == 2,
        window.len() == 2,
        domain[0] != domain[1],
        window[0] != window[1],
    ensures 
        result.len() == coef.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == coef[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Added a decreases clause to the while loop to prove termination. */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < coef.len()
        invariant
            i <= coef.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == coef@[j],
        decreases coef.len() - i
    {
        result.push(coef[i]);
        i = i + 1;
    }
    assert(result@ == coef@);
    result
}
// </vc-code>


}
fn main() {}