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
/* code modified by LLM (iteration 5): Cast `n` to `u64` before comparison so `n_int` variable is not needed. */
{
    if n < 0 {
        return false;
    }

    if n == 1 {
        return true;
    }

    if x == 1 {
        return n == 1;
    }

    let mut current_power_val: u64 = x as u64;
    let x_u64: u64 = x as u64;

    if (n as u64) == current_power_val && x_u64 == (n as u64) {
        // Handle the case where n is equal to x (and x > 1)
        return true;
    }

    ghost mut ghost_current_exponent: nat = 1;

    while current_power_val < (n as u64)
        invariant
            x_u64 > 1,
            (n as u64) > 1,
            current_power_val > 0,
            current_power_val == power(x_u64 as nat, ghost_current_exponent) as u64,
            ghost_current_exponent >= 1,
        decreases (n as u64) - current_power_val
    {
        current_power_val = current_power_val * x_u64;
        proof {
            ghost_current_exponent = ghost_current_exponent + 1;
            assert(current_power_val == power(x_u64 as nat, ghost_current_exponent) as u64);
        }
    }

    current_power_val == (n as u64)
}
// </vc-code>


}

fn main() {}