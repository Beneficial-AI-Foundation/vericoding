// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed xor_properties lemma with proper bitwise XOR proofs */
proof fn xor_properties(a: u8, b: u8)
    ensures
        (a ^ b) == (b ^ a),
        a == 0 ==> (a ^ b) == b,
        b == 0 ==> (a ^ b) == a,
        a == b ==> (a ^ b) == 0,
{
    // Commutativity of XOR
    assert(a ^ b == b ^ a) by (bit_vector);
    
    // XOR with zero
    if a == 0 {
        assert(0 ^ b == b) by (bit_vector);
    }
    if b == 0 {
        assert(a ^ 0 == a) by (bit_vector);
    }
    
    // XOR of equal values
    if a == b {
        assert(a ^ a == 0) by (bit_vector);
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
/* code modified by LLM (iteration 5): fixed loop bounds and added proper checks */
{
    let n = x1.len();
    let mut result = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == (x1@[j] ^ x2@[j]),
            forall|j: int| 0 <= j < i && x1@[j] == 0 ==> result@[j] == x2@[j],
            forall|j: int| 0 <= j < i && x2@[j] == 0 ==> result@[j] == x1@[j],
            forall|j: int| 0 <= j < i && x1@[j] == x2@[j] ==> result@[j] == 0,
        decreases n - i,
    {
        // Check bounds before accessing arrays
        assert(i < n);
        assert(i < x1.len());
        assert(i < x2.len());
        
        let a = x1[i];
        let b = x2[i];
        let xor_val = a ^ b;
        proof {
            xor_properties(a, b);
        }
        result.push(xor_val);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}