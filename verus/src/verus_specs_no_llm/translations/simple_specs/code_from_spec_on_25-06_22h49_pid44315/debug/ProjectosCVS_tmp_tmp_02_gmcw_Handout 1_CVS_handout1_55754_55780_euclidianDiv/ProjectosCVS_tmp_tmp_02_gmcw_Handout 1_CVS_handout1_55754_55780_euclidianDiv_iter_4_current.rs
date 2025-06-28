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
    let mut quotient = 0;
    let mut remainder = a;
    
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
        
        // Proof that the invariant is maintained
        assert(a == b * (quotient - 1) + (remainder + b));
        assert(a == b * quotient + remainder);
    }
    
    // At this point, remainder < b (from loop exit condition)
    // and remainder >= 0 (from invariant)
    // So we have 0 <= remainder < b
    assert(remainder < b);
    assert(remainder >= 0);
    assert(a == b * quotient + remainder);
    
    (quotient, remainder)
}

}