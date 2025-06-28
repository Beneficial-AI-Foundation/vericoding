use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn DivMod1(a: int, b: int) -> (q: int, r: int)
    requires
        b > 0 && a >= 0
    ensures
        a == b*q + r && 0 <= r < b
{
    let mut quotient = 0;
    let mut remainder = a;
    
    while remainder >= b
        invariant
            a == b * quotient + remainder,
            remainder >= 0,
            b > 0
        decreases remainder
    {
        quotient = quotient + 1;
        remainder = remainder - b;
    }
    
    assert(remainder < b); // This follows from loop exit condition
    assert(remainder >= 0); // From invariant
    assert(a == b * quotient + remainder); // From invariant
    (quotient, remainder)
}

}