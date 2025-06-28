use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Quotient(x: nat, y: nat) -> (r: int, q: int)
    requires
        y != 0
    ensures
        q * y + r == x && 0 <= r < y && 0 <= q
{
    let mut remainder = x as int;
    let mut quotient = 0int;
    let y_int = y as int;
    
    while remainder >= y_int
        invariant
            quotient * y_int + remainder == x,
            remainder >= 0,
            quotient >= 0,
            y_int > 0,
            y_int == y,
    {
        remainder = remainder - y_int;
        quotient = quotient + 1;
    }
    
    // At this point: remainder < y_int && remainder >= 0
    // Since y_int == y and y is nat, we have remainder < y
    assert(remainder < y_int);
    assert(y_int == y);
    assert(remainder >= 0);
    assert(quotient >= 0);
    assert(quotient * y_int + remainder == x);
    
    // Need to prove that remainder < y (not just y_int)
    assert(remainder < y_int && y_int == y) by {
        assert(remainder < y_int);
        assert(y_int == y);
    };
    assert(remainder < y);
    
    // Need to prove the postcondition with the correct order
    assert(quotient * y + remainder == x) by {
        assert(quotient * y_int + remainder == x);
        assert(y_int == y);
    };
    
    // Return in the order specified by the function signature: (r, q)
    // where r is remainder and q is quotient
    (remainder, quotient)
}

}