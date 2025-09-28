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
    /* code modified by LLM (iteration 4): fixed missing braces */
    let n_int = n as int;
    let total_in_cents = 800 * n_int;
    let cashback_in_cents = (n_int / 15) * 200;
    let net_in_cents = total_in_cents - cashback_in_cents;
    let net_in_dollars = net_in_cents / 100;
    net_in_dollars as i8
}
// </vc-code>


}

fn main() {}