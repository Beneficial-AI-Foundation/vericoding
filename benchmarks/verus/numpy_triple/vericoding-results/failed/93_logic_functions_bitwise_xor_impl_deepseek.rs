// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed lemma to use proper bitwise proofs */
fn lemma_xor_properties(a: u8, b: u8) 
    ensures 
        (a == 0) ==> (a ^ b == b),
        (b == 0) ==> (a ^ b == a),
        (a == b) ==> (a ^ b == 0)
{
    proof {
        assert(a == 0 ==> (a ^ b) == b) by (bit_vector);
        assert(b == 0 ==> (a ^ b) == a) by (bit_vector);
        assert(a == b ==> (a ^ b) == 0) by (bit_vector);
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
    /* code modified by LLM (iteration 5): Fixed loop invariants and array bounds */
    let n = x1.len();
    let mut result: Vec<u8> = Vec::with_capacity(n);
    let mut i: usize = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == (x1@[j] ^ x2@[j]),
            forall|j: int| 0 <= j < i && x1@[j] == 0 ==> result@[j] == x2@[j],
            forall|j: int| 0 <= j < i && x2@[j] == 0 ==> result@[j] == x1@[j],
            forall|j: int| 0 <= j < i && x1@[j] == x2@[j] ==> result@[j] == 0
        decreases n - i
    {
        assert(i < x1.len());
        assert(i < x2.len());
        let a = x1[i];
        let b = x2[i];
        lemma_xor_properties(a, b);
        result.push(a ^ b);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}