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
/* helper modified by LLM (iteration 5): remove helper as it's not used and not necessary */
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == net_amount(n as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): ensure final result fits within i8 range and matches spec before casting */
{
    let n_i32 = n as i32;

    let total_cost_val: i32 = 800 * n_i32;
    let cashback_val: i32 = (n_i32 / 15) * 200;

    let net_amount_val: i32 = total_cost_val - cashback_val;

    // Proof to show that the calculated net_amount_val matches the spec's net_amount(n as int)
    proof {
        assert(total_cost_val == total_cost(n as int));
        assert(cashback_val == cashback(n as int));
        assert(net_amount_val == net_amount(n as int));
        assert(net_amount_val >= -128 && net_amount_val <= 127);
    }

    net_amount_val as i8
}
// </vc-code>


}

fn main() {}