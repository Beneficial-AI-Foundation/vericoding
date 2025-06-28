use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn euclidianDiv(a: int, b: int) -> (q: int, r: int)
    requires
        a >= 0,
        b > 0,
        a < 0x1_0000_0000,  // Ensure a fits in u32
        b < 0x1_0000_0000   // Ensure b fits in u32
    ensures
        a == b * q + r,
        0 <= r < b
{
    let mut quotient: u32 = 0;
    let mut remainder: u32 = a as u32;
    let b_u32: u32 = b as u32;
    
    while remainder >= b_u32
        invariant
            a == b * (quotient as int) + (remainder as int),
            remainder >= 0,
            b > 0,
            quotient >= 0,
            b_u32 == b,
            remainder < 0x1_0000_0000,
            quotient < 0x1_0000_0000
        decreases remainder
    {
        quotient = quotient + 1;
        remainder = remainder - b_u32;
    }
    
    (quotient as int, remainder as int)
}

}