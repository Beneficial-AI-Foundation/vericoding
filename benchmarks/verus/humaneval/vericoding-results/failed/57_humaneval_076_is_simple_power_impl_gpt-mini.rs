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
proof fn power_succ(x: nat, y: nat)
    ensures
        power(x, (y + 1) as nat) == x * power(x, y),
{
    proof {
        reveal(power);
    }
}
// </vc-helpers>

// <vc-spec>
fn is_simple_power(x: u8, n: i8) -> (ans: bool)
    requires x > 0
    ensures ans <==> exists|y: nat| n as int == power(x as nat, y) as int
// </vc-spec>
// <vc-code>
{
    if n <= 0 {
        false
    } else {
        let x_nat: nat = x as nat;
        let target: nat = (n as int) as nat;
        if x == 1u8 {
            target == 1
        } else {
            let mut curr: nat = 1;
            let mut y: nat = 0;
            while curr <= target
                invariant
                    curr == power(x_nat, y),
                decreases
                    target - curr
            {
                if curr == target {
                    return true;
                }
                let old_curr = curr;
                let old_y = y;
                curr = old_curr * x_nat;
                y = old_y + 1;
                proof {
                    assert(old_curr == power(x_nat, old_y));
                    power_succ(x_nat, old_y);
                    assert(curr == power(x_nat, y));
                }
            }
            false
        }
    }
}
// </vc-code>


}

fn main() {}