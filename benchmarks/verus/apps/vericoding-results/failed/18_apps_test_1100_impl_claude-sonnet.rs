// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    n >= 3
}

spec fn min_jumps(n: int) -> int
    recommends valid_input(n)
{
    (n - 2) * (n - 2)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed duplicate lemma keyword */
fn lemma_min_jumps_bounds(n: i8)
    requires valid_input(n as int)
    ensures (n as int - 2) * (n as int - 2) <= 127,
            (n as int - 2) * (n as int - 2) >= -128
{
    assert(n >= 3);
    assert(n <= 127);
    assert(n as int - 2 >= 1);
    assert(n as int - 2 <= 125);
    assert((n as int - 2) * (n as int - 2) >= 1);
    assert((n as int - 2) * (n as int - 2) <= 125 * 125);
    assert(125 * 125 == 15625);
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == min_jumps(n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed arithmetic to use int operations and cast result */
    proof {
        lemma_min_jumps_bounds(n);
    }
    let temp = (n as int) - 2;
    let result_int = temp * temp;
    let result = result_int as i8;
    result
}
// </vc-code>


}

fn main() {}