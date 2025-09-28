// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn power(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 { 1 } else { x * power(x, (y - 1) as nat) }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_simple_power(x: u8, n: i8) -> (ans: bool)
    requires x > 0
    ensures ans <==> exists|y: nat| n as int == power(x as nat, y) as int
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed ghost variable syntax */
{
    if n <= 0 {
        return false;
    }
    if x == 1 {
        return n == 1;
    }
    let mut current = 1i32;
    let ghost mut ghost_exponent: nat = 0;
    while current <= n as i32 && ghost_exponent < 128
        invariant
            ghost_exponent >= 0,
            ghost_exponent < 128,
            current as int == power(x as nat, ghost_exponent) as int,
        decreases 128 - ghost_exponent as int
    {
        if current == n as i32 {
            return true;
        }
        ghost_exponent = ghost_exponent + 1;
        current = current * (x as i32);
    }
    return false;
}
// </vc-code>


}

fn main() {}