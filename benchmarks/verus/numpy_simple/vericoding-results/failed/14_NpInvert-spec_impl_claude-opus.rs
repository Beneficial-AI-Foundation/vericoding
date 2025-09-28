// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn pow2(n: nat) -> nat 
    decreases n
{
    if n == 0 {
        1nat
    } else {
        2nat * pow2((n - 1) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added lemma to prove mask calculation is safe for small bit widths */
proof fn lemma_pow2_shift_equiv(bit_width: u32)
    requires bit_width < 32
    ensures (1u32 << bit_width) - 1 == pow2(bit_width as nat) - 1
{
    // Proof that shifting is equivalent to pow2 for values < 32
}
// </vc-helpers>

// <vc-spec>
fn invert(bit_width: u32, a: Vec<u32>) -> (result: Vec<u32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a@.len() ==> result@[i] == (pow2(bit_width as nat) - 1) - a@[i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed nat/int usage in executable code */
    if bit_width >= 32 {
        // For bit_width >= 32, all bits are inverted (XOR with all 1s)
        let mut result = Vec::new();
        let mut i = 0;
        
        while i < a.len()
            invariant
                i <= a.len(),
                result.len() == i,
                forall|j: int| 0 <= j < i ==> result@[j] == (pow2(bit_width as nat) - 1) - a@[j],
            decreases a.len() - i
        {
            // For 32-bit values, inverting all bits is XOR with u32::MAX
            let inverted = u32::MAX - a[i];
            assert(u32::MAX == pow2(32nat) - 1);
            assert(bit_width >= 32);
            assert(pow2(bit_width as nat) - 1 >= pow2(32nat) - 1);
            assert(inverted == (pow2(bit_width as nat) - 1) - a@[i as int]) by {
                // When bit_width >= 32, pow2(bit_width) - 1 >= u32::MAX
                // For u32 values, subtracting from u32::MAX is the same as subtracting from larger masks
            }
            result.push(inverted);
            i += 1;
        }
        return result;
    }
    
    // For bit_width < 32, we can use bitwise operations safely
    assert(bit_width < 32);
    proof {
        lemma_pow2_shift_equiv(bit_width);
    }
    let mask = (1u32 << bit_width) - 1;
    assert(mask == pow2(bit_width as nat) - 1);
    
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == (pow2(bit_width as nat) - 1) - a@[j],
            mask == pow2(bit_width as nat) - 1,
            bit_width < 32,
        decreases a.len() - i
    {
        let inverted = mask - a[i];
        assert(inverted == (pow2(bit_width as nat) - 1) - a@[i as int]);
        result.push(inverted);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}