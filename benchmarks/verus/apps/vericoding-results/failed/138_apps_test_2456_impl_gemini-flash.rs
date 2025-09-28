// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, r: int) -> bool {
    n >= 1 && r >= 1
}

spec fn expected_result(n: int, r: int) -> int {
    if valid_input(n, r) {
        let k = if r < n - 1 { r } else { n - 1 };
        k * (k + 1) / 2 + if r >= n { 1int } else { 0int }
    } else {
        0int
    }
}

fn solve_shapes(n: i8, r: i8) -> (result: i8)
    requires valid_input(n as int, r as int)
    ensures result as int == expected_result(n as int, r as int)
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed unused empty helper section. */

// </vc-helpers>

// <vc-spec>
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): This iteration refactors the calculation to use ghost variables for intermediate int calculations and then cast the final result to i8 while ensuring the validity of the casting with assertions. */
{
    let ghost n_ghost = n as int;
    let ghost r_ghost = r as int;

    let ghost k_val: int;
    if r_ghost < n_ghost - 1 {
        k_val = r_ghost;
    } else {
        k_val = n_ghost - 1;
    }

    let ghost mut result_ghost: int = k_val * (k_val + 1) / 2;
    if r_ghost >= n_ghost {
        result_ghost = result_ghost + 1;
    }

    // Verify that the result fits within i8 before casting
    assert(result_ghost >= i8::MIN as int && result_ghost <= i8::MAX as int);
    (result_ghost as i8)
}
// </vc-code>


}

fn main() {}