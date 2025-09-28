// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added helper for bitwise xor with proper spec */
fn xor_byte(a: u8, b: u8) -> (c: u8)
    ensures c == (a ^ b),
{
    a ^ b
}
// </vc-helpers>

// <vc-spec>
fn bitwise_xor(a: Vec<u8>, b: Vec<u8>) -> (result: Vec<u8>)
    requires 
        a.len() == b.len(),
        a.len() > 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a@.len() ==> result@[i] == a@[i] ^ b@[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed loop invariant to include sequence length constraints */
    let mut result = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a@.len(),
            result@.len() == i,
            a@.len() == b@.len(),
            forall|j: int| 0 <= j < i ==> result@[j] == a@[j] ^ b@[j],
        decreases a@.len() - i,
    {
        result.push(xor_byte(a[i], b[i]));
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}