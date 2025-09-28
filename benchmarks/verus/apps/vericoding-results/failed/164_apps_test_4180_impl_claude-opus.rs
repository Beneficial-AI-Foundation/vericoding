// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    1 <= n <= 10000
}

spec fn valid_change(change: int) -> bool {
    0 <= change <= 999
}

spec fn correct_change(n: int) -> int
    recommends valid_input(n)
{
    (1000 - n % 1000) % 1000
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (change: i8)
    requires valid_input(n as int)
    ensures 
        valid_change(change as int) &&
        change as int == correct_change(n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix type mismatch - n is i8 but needs to handle values up to 10000 */
    let n_int = n as int;
    let remainder = n_int % 1000;
    let change_int = if remainder == 0 {
        0
    } else {
        1000 - remainder
    };
    assert(change_int == correct_change(n_int));
    assert(0 <= change_int <= 999);
    assert(change_int <= 127);
    let change = change_int as i8;
    change
}
// </vc-code>


}

fn main() {}