// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed placeholder helper section as no helpers are needed. */
// </vc-helpers>

// <vc-spec>
fn bitwise_xor(x1: Vec<u32>, x2: Vec<u32>) -> (result: Vec<u32>)
    requires 
        x1.len() == x2.len(),
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] ^ x2[i]),
        forall|i: int| 0 <= i < result.len() && x1[i] == 0 ==> result[i] == x2[i],
        forall|i: int| 0 <= i < result.len() && x2[i] == 0 ==> result[i] == x1[i],
        forall|i: int| 0 <= i < result.len() && x1[i] == x2[i] ==> result[i] == 0,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Added decreases clause to the loop to satisfy the verifier's requirement. */
{
    let mut result: Vec<u32> = Vec::new();
    let len = x1.len();
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i as int <= len as int,
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result[j] == (x1[j] ^ x2[j]),
        decreases len - i
    {
        result.push(x1[i] ^ x2[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}