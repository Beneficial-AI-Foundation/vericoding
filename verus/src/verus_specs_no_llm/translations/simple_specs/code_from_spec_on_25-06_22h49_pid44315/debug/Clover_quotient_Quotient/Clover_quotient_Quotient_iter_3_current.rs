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
    let mut quotient = 0;
    let y_int = y as int;
    
    while remainder >= y_int
        invariant
            quotient * y_int + remainder == x,
            remainder >= 0,
            quotient >= 0,
            y_int > 0,
            y_int == y,
    {
        proof {
            assert(remainder >= y_int);
            assert(y_int > 0);
            assert(remainder - y_int >= 0);
        }
        remainder = remainder - y_int;
        quotient = quotient + 1;
        
        proof {
            assert(quotient * y_int + remainder == (quotient - 1) * y_int + (remainder + y_int));
            assert((quotient - 1) * y_int + (remainder + y_int) == (quotient - 1) * y_int + remainder + y_int);
            assert((quotient - 1) * y_int + remainder + y_int == x);
        }
    }
    
    proof {
        assert(remainder < y_int);
        assert(remainder >= 0);
        assert(quotient >= 0);
        assert(quotient * y_int + remainder == x);
        assert(y_int == y);
        assert(quotient * y + remainder == x);
        assert(0 <= remainder < y);
    }
    
    return (remainder, quotient);
}

}

Wait, I need to check the postcondition more carefully. The postcondition states `q * y + r == x && 0 <= r < y && 0 <= q`, and the return type is `(r: int, q: int)`. This means the first returned value is `r` and the second is `q`. So if we return `(remainder, quotient)`, then `r = remainder` and `q = quotient`, which means the postcondition should be `quotient * y + remainder == x`.

The current invariant and logic look correct, but let me double-check the proof assertions to ensure they align properly with the postcondition:

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
    let mut quotient = 0;
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
    
    (remainder, quotient)
}

}