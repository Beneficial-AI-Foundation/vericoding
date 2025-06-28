use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn euclidianDiv(a: int, b: int) -> (q: int, r: int)
    requires
        a >= 0,
        b > 0
    ensures
        a == b * q + r,
        0 <= r < b
{
    let mut quotient: int = 0;
    let mut remainder: int = a;
    
    while remainder >= b
        invariant
            a == b * quotient + remainder,
            remainder >= 0,
            b > 0,
            quotient >= 0
        decreases remainder
    {
        quotient = quotient + 1;
        remainder = remainder - b;
    }
    
    (quotient, remainder)
}

}