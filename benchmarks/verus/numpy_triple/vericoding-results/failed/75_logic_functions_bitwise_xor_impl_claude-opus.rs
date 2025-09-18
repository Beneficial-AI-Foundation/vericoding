// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Added assertions to help verify XOR properties */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            i <= x1.len(),
            x1.len() == x2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == (x1@[j] ^ x2@[j]),
        decreases x1.len() - i,
    {
        let xor_val = x1[i] ^ x2[i];
        result.push(xor_val);
        
        proof {
            assert(result@[i as int] == xor_val);
            assert(result@[i as int] == (x1@[i as int] ^ x2@[i as int]));
            assert(x1@[i as int] == 0 ==> (x1@[i as int] ^ x2@[i as int]) == x2@[i as int]);
            assert(x2@[i as int] == 0 ==> (x1@[i as int] ^ x2@[i as int]) == x1@[i as int]);
            assert(x1@[i as int] == x2@[i as int] ==> (x1@[i as int] ^ x2@[i as int]) == 0);
        }
        
        i += 1;
    }
    
    proof {
        assert(result.len() == x1.len());
        assert(forall|j: int| 0 <= j < result.len() ==> result@[j] == (x1@[j] ^ x2@[j]));
    }
    
    result
}
// </vc-code>

}
fn main() {}