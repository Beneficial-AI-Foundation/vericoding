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
proof fn lemma_cashback_property(m: int)
    requires valid_input(m) && m >= 15,
    ensures net_amount(m) == net_amount(m - 15) + 800 * 15 - 200
{
    assert(net_amount(m) == 800 * m - (m / 15) * 200);
    assert(net_amount(m - 15) == 800 * (m - 15) - ((m - 15) / 15) * 200);
    assert((m - 15) / 15 == m / 15 - 1);
    assert(net_amount(m - 15) == 800 * m - 12000 - 200 * (m / 15) + 200);
    assert(net_amount(m - 15) == net_amount(m) - 800 * 15 + 200);
    assert(net_amount(m) == net_amount(m - 15) + 800 * 15 - 200);
}

proof fn lemma_base_case(n: int)
    requires valid_input(n) && n == 1,
    ensures net_amount(n) == 800
{
    assert(total_cost(n) == 800);
    assert(cashback(n) == 0);
    assert(net_amount(n) == 800);
}

proof fn compute_net_amount(n: int) -> (result: int)
    requires valid_input(n),
    ensures result == net_amount(n)
{
    let cost: int = 800 * n;
    let cb: int = (n / 15) * 200;
    let net: int = cost - cb;
    net
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == net_amount(n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error by removing ghost block syntax */
    let n_int: int = n as int;
    let result_int: int = compute_net_amount(n_int);
    let result: i8 = ((800 * n) - ((n as int / 15) * 200)) as i8;
    result
}
// </vc-code>


}

fn main() {}