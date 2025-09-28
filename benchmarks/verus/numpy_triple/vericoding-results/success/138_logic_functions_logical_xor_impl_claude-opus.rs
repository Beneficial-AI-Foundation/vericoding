// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_logical_xor(x1: Vec<bool>, x2: Vec<bool>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] != x2[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to while loop */
    let mut result = Vec::new();
    let n = x1.len();
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == x1.len(),
            n == x2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (x1[j] != x2[j]),
        decreases n - i
    {
        let xor_val = x1[i] != x2[i];
        result.push(xor_val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}