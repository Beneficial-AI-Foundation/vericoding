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
    /* code modified by LLM (iteration 2): added decreases clause to while loop */
    let mut result = Vec::new();
    let n = x1.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == x1.len(),
            n == x2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < x2.len() ==> x2@[j] != 0.0,
        decreases n - i
    {
        let quotient = x1[i] / x2[i];
        result.push(quotient);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}