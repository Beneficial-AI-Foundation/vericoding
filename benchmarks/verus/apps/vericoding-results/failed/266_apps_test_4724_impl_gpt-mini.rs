// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(r: int, g: int) -> bool {
    0 <= r <= 4500 && 0 <= g <= 4500
}

spec fn required_performance(r: int, g: int) -> int {
    2 * g - r
}

spec fn correct_result(r: int, g: int, p: int) -> bool {
    (r + p) == 2 * g
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): relate required_performance to i8 arithmetic */
proof fn perf_is_2g_minus_r(r: i8, g: i8)
    ensures
        required_performance(r as int, g as int) == (2 * g - r) as int,
    decreases
        0,
{
    proof {
        assert(required_performance(r as int, g as int) == 2 * (g as int) - (r as int));
        assert(2 * (g as int) - (r as int) == (2 * g - r) as int);
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(r: i8, g: i8) -> (result: i8)
    requires 
        valid_input(r as int, g as int)
    ensures 
        result as int == required_performance(r as int, g as int) &&
        correct_result(r as int, g as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute p with i8 arithmetic and prove correctness */
    let result: i8 = 2 * g - r;
    proof {
        perf_is_2g_minus_r(r, g);
        assert(result as int == required_performance(r as int, g as int));
    }
    result
}

// </vc-code>


}

fn main() {}