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
    /* code modified by LLM (iteration 4): fix type error by using usize index directly */
    let mut result = Vec::new();
    let n = x1.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            i == result.len(),
            x1.len() == x2.len(),
            x1.len() == n,
            forall|j: int| 0 <= j < i as int ==> result@[j] == (x1@[j] != x2@[j]),
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