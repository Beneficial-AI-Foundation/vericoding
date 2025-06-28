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
    
    (remainder, quotient)
}

}