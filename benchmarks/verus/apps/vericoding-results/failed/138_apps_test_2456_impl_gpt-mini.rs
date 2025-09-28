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
/* helper modified by LLM (iteration 5): convert i8 to int in spec */
spec fn i8_to_int(x: i8) -> int {
    x as int
}

// </vc-helpers>

// <vc-spec>
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute expected result using int arithmetic and prove equality */
    let n_int: int = n as int;
    let r_int: int = r as int;
    let k_int: int = if r_int < n_int - 1 { r_int } else { n_int - 1 };
    let sum_int: int = k_int * (k_int + 1) / 2 + if r_int >= n_int { 1 } else { 0 };
    let result: i8 = sum_int as i8;
    proof {
        assert(n_int == i8_to_int(n));
        assert(r_int == i8_to_int(r));
        assert(sum_int == expected_result(n_int, r_int));
        assert((result as int) == expected_result(n_int, r_int));
    }
    result
}

// </vc-code>


}

fn main() {}