// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): kept simple helper function for coefficient computation */
fn compute_coefficient(coef: f64, domain_0: f64, domain_1: f64, window_0: f64, window_1: f64) -> (result: f64)
    ensures
        result == coef,
{
    coef
}
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
    /* code modified by LLM (iteration 3): added bounds checks for domain and window array access */
    let mut result: Vec<f64> = Vec::new();
    let mut i = 0;
    while i < coef.len()
        invariant
            i <= coef.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == coef[j],
            domain.len() == 2,
            window.len() == 2,
        decreases coef.len() - i
    {
        let transformed_coef = compute_coefficient(coef[i], domain[0], domain[1], window[0], window[1]);
        result.push(transformed_coef);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}