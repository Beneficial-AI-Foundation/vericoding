// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(r: int, g: int, b: int) -> bool {
    r >= 1 && g >= 1 && b >= 1
}

spec fn max_of_3(r: int, g: int, b: int) -> int {
    if r >= g && r >= b {
        r
    } else if g >= r && g >= b {
        g
    } else {
        b
    }
}

spec fn can_arrange(r: int, g: int, b: int) -> bool
    recommends valid_input(r, g, b)
{
    let max_count = max_of_3(r, g, b);
    let total = r + g + b;
    2 * max_count <= total + 1
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn check_lamp_arrangement(r: i8, g: i8, b: i8) -> (result: bool)
    requires valid_input(r as int, g as int, b as int)
    ensures result == can_arrange(r as int, g as int, b as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Implement the arrangement check using i32 casting to avoid int ghost type errors and ensure logic matches spec */
{
    let r_exec = r as i32;
    let g_exec = g as i32;
    let b_exec = b as i32;
    let max_count = if r_exec >= g_exec && r_exec >= b_exec {
        r_exec
    } else if g_exec >= r_exec && g_exec >= b_exec {
        g_exec
    } else {
        b_exec
    };
    let total = r_exec + g_exec + b_exec;
    let lhs = 2 * max_count;
    let rhs = total + 1;
    lhs <= rhs
}
// </vc-code>


}

fn main() {}