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

// </vc-helpers>

// <vc-spec>
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): use i32 for intermediate calculations to avoid int in non-ghost code */
    let n_i32 = n as i32;
    let r_i32 = r as i32;
    let k = if r_i32 < n_i32 - 1 { r_i32 } else { n_i32 - 1 };
    let sum = k * (k + 1) / 2;
    let extra = if r_i32 >= n_i32 { 1 } else { 0 };
    let total = sum + extra;
    total as i8
}
// </vc-code>


}

fn main() {}