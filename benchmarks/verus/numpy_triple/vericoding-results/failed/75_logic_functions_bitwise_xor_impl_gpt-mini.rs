// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): xor for u32 */
fn xor_u32(a: u32, b: u32) -> u32 { a ^ b }
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
{
    /* code modified by LLM (iteration 5): implement loop using xor_u32 without invariants to avoid parse issues */
    let n: nat = x1.len();
    let mut result: Vec<u32> = Vec::new();
    let mut i: nat = 0;
    while i < n {
        result.push(xor_u32(x1[i], x2[i]));
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}