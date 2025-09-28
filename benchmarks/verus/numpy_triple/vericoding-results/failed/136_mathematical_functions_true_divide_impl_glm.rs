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
    /* code modified by LLM (iteration 5): fixed indexing by using [] instead of @ for Vec access */
    let n = x1.len();
    let mut result = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            x1.len() == n,
            x2.len() == n,
        decreases n - i
    {
        result.push(x1[i] / x2[i]);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}