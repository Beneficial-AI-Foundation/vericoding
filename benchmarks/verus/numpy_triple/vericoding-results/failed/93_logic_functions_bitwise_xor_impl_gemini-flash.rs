// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers are needed for this problem. */

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
    /* code modified by LLM (iteration 5): Replaced `vec![0u8; len as usize]` with `Vec::new();` and then resizing it to `len`. */
    let len = x1.len();
    let mut result: Vec<u8> = Vec::new();
    result.resize(len, 0u8);

    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i as int <= len as int,
            result.len() == len,
            forall|j: int| 0 <= j < i as int ==> result@[j] == (x1@[j] ^ x2@[j]),
            result.len() == len,
    {
        result.set(i, x1[i] ^ x2[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}