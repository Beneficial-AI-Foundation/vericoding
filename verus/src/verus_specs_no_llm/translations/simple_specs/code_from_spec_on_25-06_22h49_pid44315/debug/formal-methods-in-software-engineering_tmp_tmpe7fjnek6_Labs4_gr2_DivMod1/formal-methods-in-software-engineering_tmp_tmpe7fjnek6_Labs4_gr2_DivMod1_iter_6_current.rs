use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn DivMod1(a: int, b: int) -> (q: int, r: int)
    requires
        b > 0 && a >= 0 && a < 0x1_0000_0000 && b < 0x1_0000_0000
    ensures
        a == b*q + r && 0 <= r < b
{
    let mut quotient: u32 = 0;
    let mut remainder: u32 = a as u32;
    let b_u32: u32 = b as u32;
    
    while remainder >= b_u32
        invariant
            a == b * (quotient as int) + (remainder as int),
            remainder >= 0,
            b > 0,
            quotient < 0x1_0000_0000,
            remainder < 0x1_0000_0000,
            b_u32 == b
        decreases remainder
    {
        proof {
            // Prove that remainder will decrease
            assert(remainder >= b_u32);
            assert(b_u32 > 0);
            assert(remainder - b_u32 < remainder);
        }
        quotient = quotient + 1;
        remainder = remainder - b_u32;
    }
    
    // These assertions help verify the postcondition
    assert(remainder < b_u32); // This follows from loop exit condition
    assert(remainder >= 0); // From invariant
    assert(a == b * (quotient as int) + (remainder as int)); // From invariant
    assert(b_u32 == b); // From invariant
    assert((remainder as int) < b); // Combining the above
    
    (quotient as int, remainder as int)
}

}