// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn bitwise_xor(x1: Vec<u8>, x2: Vec<u8>) -> (result: Vec<u8>)
    requires 
        x1.len() == x2.len(),
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result@[i] == (x1@[i] ^ x2@[i]),
        forall|i: int| 0 <= i < result.len() && x1@[i] == 0 ==> result@[i] == x2@[i],
        forall|i: int| 0 <= i < result.len() && x2@[i] == 0 ==> result@[i] == x1@[i],
        forall|i: int| 0 <= i < result.len() && x1@[i] == x2@[i] ==> result@[i] == 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to while loop */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == (x1@[j] ^ x2@[j]),
        decreases x1.len() - i
    {
        let xor_val = x1[i] ^ x2[i];
        result.push(xor_val);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}