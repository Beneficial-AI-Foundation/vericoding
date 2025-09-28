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
/* helper modified by LLM (iteration 5): removed helper, as it was not needed */
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (change: i8)
    requires valid_input(n as int)
    ensures 
        valid_change(change as int) &&
        change as int == correct_change(n as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix compiler error by removing `n_int: int` and directly using `n as int` in the calculation.*/
{
    let change_int: int = (1000 - (n as int) % 1000) % 1000;

    // Proof of correctness for the change calculation
    proof {
        assert(valid_input(n as int));
        assert(change_int == correct_change(n as int));
        assert(valid_change(change_int));
    }

    let change_i8: i8 = change_int as i8;
    change_i8
}
// </vc-code>


}

fn main() {}