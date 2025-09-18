// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec wrapper for xor */
spec fn bv_xor(a: u32, b: u32) -> u32 { a ^ b }
/* helper modified by LLM (iteration 5): lemma 0 ^ b == b */
proof fn lemma_xor_zero_left(b: u32)
    ensures 0u32 ^ b == b
{ }
/* helper modified by LLM (iteration 5): lemma a ^ 0 == a */
proof fn lemma_xor_zero_right(a: u32)
    ensures a ^ 0u32 == a
{ }
/* helper modified by LLM (iteration 5): lemma a ^ a == 0 */
proof fn lemma_xor_self_zero(a: u32)
    ensures a ^ a == 0u32
{ }
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
    /* code modified by LLM (iteration 5): implement XOR with strong invariants to satisfy zero/equal cases */
    let n = x1.len();
    let mut res: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            x1.len() == n,
            x2.len() == n,
            i <= n,
            res.len() == i,
            forall|j: int| 0 <= j && j < i as int ==> res@[j] == (x1[j] ^ x2[j]),
            forall|j: int| 0 <= j && j < i as int && x1[j] == 0u32 ==> res@[j] == x2[j],
            forall|j: int| 0 <= j && j < i as int && x2[j] == 0u32 ==> res@[j] == x1[j],
            forall|j: int| 0 <= j && j < i as int && x1[j] == x2[j] ==> res@[j] == 0u32
        decreases n - i
    {
        let v: u32 = x1[i] ^ x2[i];
        proof {
            assert(x1[i] == 0u32 ==> v == x2[i]);
            assert(x2[i] == 0u32 ==> v == x1[i]);
            assert(x1[i] == x2[i] ==> v == 0u32);
        }
        res.push(v);
        i += 1;
    }
    res
}
// </vc-code>

}
fn main() {}