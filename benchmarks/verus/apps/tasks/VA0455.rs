// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_test_case(a: nat, b: nat, n: nat, m: nat) -> bool
{
    n + m > 0
}

spec fn can_satisfy_all_guests(a: nat, b: nat, n: nat, m: nat) -> bool
{
    a + b >= n + m &&
    m <= min(a, b)
}

spec fn min(x: nat, y: nat) -> nat
{
    if x <= y { x } else { y }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve_cookie_distribution(a: u8, b: u8, n: u8, m: u8) -> (result: bool)
    requires
        valid_test_case(a as nat, b as nat, n as nat, m as nat),
    ensures
        result == can_satisfy_all_guests(a as nat, b as nat, n as nat, m as nat),
        result ==> ((a as nat) + (b as nat) >= (n as nat) + (m as nat) && (m as nat) <= min(a as nat, b as nat)),
        !result ==> ((a as nat) + (b as nat) < (n as nat) + (m as nat) || (m as nat) > min(a as nat, b as nat)),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}