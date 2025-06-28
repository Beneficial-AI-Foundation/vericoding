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
    
    proof {
        assert(remainder < y_int);
        assert(remainder >= 0);
        assert(quotient >= 0);
        assert(quotient * y_int + remainder == x);
        assert(y_int == y);
        // Since y_int == y, we have quotient * y + remainder == x
        assert(quotient * y + remainder == x);
        assert(0 <= remainder < y);
        assert(0 <= quotient);
    }
    
    (remainder, quotient)
}

}