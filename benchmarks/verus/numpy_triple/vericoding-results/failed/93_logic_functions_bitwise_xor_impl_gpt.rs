// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): XOR identity 0 ^ b == b */
proof fn xor_zero_left(b: u8)
    ensures
        0u8 ^ b == b,
{
    assert(0u8 ^ b == b);
}

/* helper modified by LLM (iteration 5): XOR identity b ^ 0 == b */
proof fn xor_zero_right(b: u8)
    ensures
        b ^ 0u8 == b,
{
    assert(b ^ 0u8 == b);
}

/* helper modified by LLM (iteration 5): XOR idempotence b ^ b == 0 */
proof fn xor_self_zero(b: u8)
    ensures
        b ^ b == 0u8,
{
    assert(b ^ b == 0u8);
}
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
    /* code modified by LLM (iteration 5): implement elementwise XOR with loop invariants and direct bitvector reasoning */
    let n = x1.len();
    let mut result: Vec<u8> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            n == x1.len(),
            n == x2.len(),
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> result@[j] == (x1@[j] ^ x2@[j]),
            forall|j: int| 0 <= j < result.len() && x1@[j] == 0 ==> result@[j] == x2@[j],
            forall|j: int| 0 <= j < result.len() && x2@[j] == 0 ==> result@[j] == x1@[j],
            forall|j: int| 0 <= j < result.len() && x1@[j] == x2@[j] ==> result@[j] == 0,
        decreases n - i
    {
        let oi = i;
        let v = x1[oi] ^ x2[oi];
        result.push(v);
        proof {
            let k = oi as int;
            assert(0 <= k && k < result.len());
            // After push, the new element at index k equals v
            assert(result@[k] == (x1@[k] ^ x2@[k]));
            if x1@[k] == 0u8 {
                assert((x1@[k] ^ x2@[k]) == x2@[k]);
                assert(result@[k] == x2@[k]);
            }
            if x2@[k] == 0u8 {
                assert((x1@[k] ^ x2@[k]) == x1@[k]);
                assert(result@[k] == x1@[k]);
            }
            if x1@[k] == x2@[k] {
                assert((x1@[k] ^ x1@[k]) == 0u8);
                assert(result@[k] == 0u8);
            }
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}