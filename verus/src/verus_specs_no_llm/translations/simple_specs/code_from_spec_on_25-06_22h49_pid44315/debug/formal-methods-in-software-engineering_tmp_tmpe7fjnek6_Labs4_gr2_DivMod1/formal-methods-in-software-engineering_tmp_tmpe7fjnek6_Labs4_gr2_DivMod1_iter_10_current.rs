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
            remainder as int >= 0,
            quotient as int >= 0,
            b_u32 as int == b,
            b_u32 > 0,
            quotient as int * b <= a,
            remainder as int <= a
        decreases remainder
    {
        remainder = remainder - b_u32;
        quotient = quotient + 1;
    }
    
    (quotient as int, remainder as int)
}

}