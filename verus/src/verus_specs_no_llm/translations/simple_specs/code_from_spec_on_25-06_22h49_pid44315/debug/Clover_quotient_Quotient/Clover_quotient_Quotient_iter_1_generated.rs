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
    
    while remainder >= y
        invariant
            quotient * y + remainder == x,
            remainder >= 0,
            quotient >= 0,
    {
        remainder = remainder - y;
        quotient = quotient + 1;
    }
    
    return (remainder, quotient);
}

}