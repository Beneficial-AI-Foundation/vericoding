// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): xor_zero_right proof for u8 */
fn xor_zero_right(a: u8, b: u8)
    ensures
        (a == 0u8) ==> (a ^ b == b),
{
    proof {
        if a == 0u8 {
            assert(a ^ b == b);
        }
    }
}

/* helper modified by LLM (iteration 5): xor_zero_left proof for u8 */
fn xor_zero_left(a: u8, b: u8)
    ensures
        (b == 0u8) ==> (a ^ b == a),
{
    proof {
        if b == 0u8 {
            assert(a ^ b == a);
        }
    }
}

/* helper modified by LLM (iteration 5): xor_self_zero proof for u8 */
fn xor_self_zero(a: u8)
    ensures
        (a ^ a) == 0u8,
{
    proof {
        assert(a ^ a == 0u8);
    }
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
    /* code modified by LLM (iteration 5): implement elementwise xor using usize loop */
    let n = x1.len();
    let mut res: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            res.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> res@[j] == (x1@[j] ^ x2@[j]),
        decreases n - i
    {
        let a = x1[i];
        let b = x2[i];
        res.push(a ^ b);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}