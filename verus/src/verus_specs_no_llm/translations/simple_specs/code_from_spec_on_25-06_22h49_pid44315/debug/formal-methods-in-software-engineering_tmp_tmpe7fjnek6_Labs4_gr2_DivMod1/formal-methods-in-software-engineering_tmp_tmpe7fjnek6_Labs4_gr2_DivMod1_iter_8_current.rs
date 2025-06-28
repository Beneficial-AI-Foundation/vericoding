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
    
    proof {
        // Establish that our casts are safe
        assert(0 <= a < 0x1_0000_0000);
        assert(0 < b < 0x1_0000_0000);
        assert(a as u32 as int == a);
        assert(b as u32 as int == b);
    }
    
    while remainder >= b_u32
        invariant
            a == b * (quotient as int) + (remainder as int),
            remainder < 0x1_0000_0000,
            quotient < 0x1_0000_0000,
            b_u32 == b as u32,
            b_u32 > 0,
            b > 0,
            b_u32 as int == b,
            remainder as int >= 0,
            quotient as int >= 0
        decreases remainder
    {
        proof {
            assert(remainder >= b_u32);
            assert(b_u32 > 0);
            assert(remainder - b_u32 < remainder);
            // Prove that subtraction won't underflow
            assert(remainder as int >= b_u32 as int);
            assert(remainder as int >= b);
            // Prove that addition won't overflow
            assert(quotient < 0x1_0000_0000 - 1);
        }
        remainder = remainder - b_u32;
        quotient = quotient + 1;
        
        proof {
            // Help Verus understand the arithmetic
            assert(a == b * ((quotient - 1) as int) + ((remainder + b_u32) as int));
            assert((remainder + b_u32) as int == (remainder as int) + (b_u32 as int));
            assert((remainder + b_u32) as int == (remainder as int) + b);
            assert(a == b * ((quotient - 1) as int) + (remainder as int) + b);
            assert(a == b * (((quotient - 1) as int) + 1) + (remainder as int));
            assert(a == b * (quotient as int) + (remainder as int));
        }
    }
    
    proof {
        assert(remainder < b_u32);
        assert(b_u32 == b as u32);
        assert(b_u32 as int == b);
        assert((remainder as int) < (b_u32 as int));
        assert((remainder as int) < b);
        assert(remainder as int >= 0);
        assert(a == b * (quotient as int) + (remainder as int));
    }
    
    (quotient as int, remainder as int)
}

}