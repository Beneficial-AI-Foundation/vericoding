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

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, v: i8) -> (result: i8)
    requires valid_input(n as int, v as int)
    ensures result as int == min_cost(n as int, v as int)
// </vc-spec>
// <vc-code>
{
    let n_int: int = n as int;
    let v_int: int = v as int;

    let req: int = n_int - 1;

    if req <= v_int {
        req as i8
    } else {
        let remaining_initial: int = req - v_int;
        let mut current_cost: int = v_int;

        let mut i: int = 0;

        while i < remaining_initial
            invariant
                current_cost == v_int + i * (i + 3) / 2,
                i <= remaining_initial,
                remaining_initial >= 0,
            decreases remaining_initial - i
        {
            current_cost = current_cost + (i + 2);
            i = i + 1;
        }

        current_cost as i8
    }
}
// </vc-code>


}

fn main() {}