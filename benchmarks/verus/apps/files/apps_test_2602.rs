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
fn solve_cookie_distribution(a: nat, b: nat, n: nat, m: nat) -> (result: bool)
    requires
        valid_test_case(a, b, n, m),
    ensures
        result == can_satisfy_all_guests(a, b, n, m),
        result ==> (a + b >= n + m && m <= min(a, b)),
        !result ==> (a + b < n + m || m > min(a, b)),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}