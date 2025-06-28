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
        proof {
            // Help Verus see that the arithmetic is preserved
            assert(a == b * quotient + remainder);
            assert(remainder >= b);
        }
        quotient = quotient + 1;
        remainder = remainder - b;
        proof {
            // Prove the invariant is maintained
            assert(a == b * (quotient - 1) + (remainder + b));
            assert(a == b * quotient + remainder);
        }
    }
    
    proof {
        // After the loop, remainder < b (from loop condition)
        // and we still have a == b * quotient + remainder
        assert(remainder < b);
        assert(remainder >= 0);
        assert(a == b * quotient + remainder);
    }
    
    (quotient, remainder)
}

}