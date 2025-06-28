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
            remainder < 0x1_0000_0000,
            quotient < 0x1_0000_0000,
            b_u32 == b as u32,
            b_u32 > 0,
            b > 0
        decreases remainder
    {
        proof {
            assert(remainder >= b_u32);
            assert(b_u32 > 0);
            assert(remainder - b_u32 < remainder);
        }
        remainder = remainder - b_u32;
        quotient = quotient + 1;
    }
    
    proof {
        assert(remainder < b_u32);
        assert(b_u32 == b as u32);
        assert(b_u32 as int == b);
        assert((remainder as int) < (b_u32 as int));
        assert((remainder as int) < b);
        assert(a == b * (quotient as int) + (remainder as int));
    }
    
    (quotient as int, remainder as int)
}

}