// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_logical_and(x1: Vec<bool>, x2: Vec<bool>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] && x2[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed invariant to ensure i < x1.len() and i < x2.len() in loop body */
    let mut result = Vec::new();
    let n = x1.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == x1.len(),
            n == x2.len(),
            i == result.len(),
            forall|j: int| 0 <= j < i ==> result[j] == (x1[j] && x2[j]),
        decreases n - i
    {
        let val = x1[i] && x2[i];
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}