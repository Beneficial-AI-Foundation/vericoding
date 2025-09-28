// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, v: int) -> bool {
    2 <= n <= 100 && 1 <= v <= 100
}

spec fn min_cost(n: int, v: int) -> int {
    let req = n - 1;
    if req <= v {
        req
    } else {
        let remaining = req - v;
        v + remaining * (remaining + 3) / 2
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Add proper proof implementation for bounds */
proof fn arithmetic_bounds(n: i8, v: i8)
    requires valid_input(n as int, v as int)
    ensures
        (n - 1) as int >= 1,
        (n - 1) as int <= 99,
        v as int >= 1,
        v as int <= 100
{
}

proof fn remaining_bounds(n: i8, v: i8, remaining: i8)
    requires
        valid_input(n as int, v as int),
        remaining == (n - 1) - v,
        remaining > 0
    ensures
        remaining as int >= 1,
        remaining as int <= 98,
        (remaining as int) * (remaining as int + 3) <= 9898,
        v as int + (remaining as int) * (remaining as int + 3) / 2 <= 5049
{
    proof {
        let r = remaining as int;
        assert(r >= 1);
        assert(r <= 98);
        assert(r * (r + 3) <= 98 * 101);
        assert(98 * 101 == 9898);
        assert(v as int <= 100);
        assert(r * (r + 3) / 2 <= 4949);
        assert(v as int + r * (r + 3) / 2 <= 100 + 4949);
        assert(100 + 4949 == 5049);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, v: i8) -> (result: i8)
    requires valid_input(n as int, v as int)
    ensures result as int == min_cost(n as int, v as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Use ghost variables for int arithmetic */
    let req = n - 1;
    if req <= v {
        proof {
            arithmetic_bounds(n, v);
        }
        req
    } else {
        let remaining = req - v;
        proof {
            arithmetic_bounds(n, v);
            remaining_bounds(n, v, remaining);
            let ghost result_int = v as int + (remaining as int) * (remaining as int + 3) / 2;
            assert(result_int <= 5049);
        }
        let result = v + (remaining * (remaining + 3)) / 2;
        result
    }
}
// </vc-code>


}

fn main() {}