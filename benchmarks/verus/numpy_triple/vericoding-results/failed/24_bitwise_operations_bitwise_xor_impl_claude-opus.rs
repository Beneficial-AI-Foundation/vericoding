// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn bitwise_xor(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x1.len() ==> x1[i] >= 0,
        forall|i: int| 0 <= i < x2.len() ==> x2[i] >= 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] ^ x2[i]),
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,
        forall|i: int| 0 <= i < result.len() && x1[i] == 0 ==> result[i] == x2[i],
        forall|i: int| 0 <= i < result.len() && x2[i] == 0 ==> result[i] == x1[i],
        forall|i: int| 0 <= i < result.len() && x1[i] == x2[i] ==> result[i] == 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type mismatches by casting usize to int for vector indexing */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    while i < x1.len()
        invariant
            i <= x1.len(),
            result.len() == i,
            x1.len() == x2.len(),
            forall|j: int| 0 <= j < i ==> result[j] == (x1[j] ^ x2[j]),
            forall|j: int| 0 <= j < i ==> result[j] >= 0,
            forall|j: int| 0 <= j < x1.len() ==> x1[j] >= 0,
            forall|j: int| 0 <= j < x2.len() ==> x2[j] >= 0,
        decreases x1.len() - i
    {
        let xor_val = x1[i as int] ^ x2[i as int];
        
        proof {
            // XOR of two non-negative integers is non-negative
            assert(x1[i as int] >= 0);
            assert(x2[i as int] >= 0);
            // Verus should understand that XOR of non-negative integers is non-negative
            assert((x1[i as int] ^ x2[i as int]) >= 0);
            
            // XOR properties
            if x1[i as int] == 0 {
                // 0 ^ x = x
                assert((0 ^ x2[i as int]) == x2[i as int]);
                assert(xor_val == x2[i as int]);
            }
            if x2[i as int] == 0 {
                // x ^ 0 = x
                assert((x1[i as int] ^ 0) == x1[i as int]);
                assert(xor_val == x1[i as int]);
            }
            if x1[i as int] == x2[i as int] {
                // x ^ x = 0
                assert((x1[i as int] ^ x1[i as int]) == 0);
                assert(xor_val == 0);
            }
        }
        
        result.push(xor_val);
        
        assert(result[i as int] == (x1[i as int] ^ x2[i as int]));
        
        i += 1;
    }
    
    // Final proof to establish postconditions
    proof {
        assert(result.len() == x1.len());
        assert forall|j: int| 0 <= j < result.len() implies result[j] == (x1[j] ^ x2[j]) by {
            assert(result[j] == (x1[j] ^ x2[j]));
        }
        assert forall|j: int| 0 <= j < result.len() && x1[j] == 0 implies result[j] == x2[j] by {
            assert(result[j] == (x1[j] ^ x2[j]));
            assert((0 ^ x2[j]) == x2[j]);
        }
        assert forall|j: int| 0 <= j < result.len() && x2[j] == 0 implies result[j] == x1[j] by {
            assert(result[j] == (x1[j] ^ x2[j]));
            assert((x1[j] ^ 0) == x1[j]);
        }
        assert forall|j: int| 0 <= j < result.len() && x1[j] == x2[j] implies result[j] == 0 by {
            assert(result[j] == (x1[j] ^ x2[j]));
            assert((x1[j] ^ x1[j]) == 0);
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}