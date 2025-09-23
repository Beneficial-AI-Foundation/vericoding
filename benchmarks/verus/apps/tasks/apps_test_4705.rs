// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    1 <= n <= 100
}

spec fn total_cost(n: int) -> int
    recommends valid_input(n)
{
    800 * n
}

spec fn cashback(n: int) -> int
    recommends valid_input(n)
{
    (n / 15) * 200
}

spec fn net_amount(n: int) -> int
    recommends valid_input(n)
{
    total_cost(n) - cashback(n)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == net_amount(n as int)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}