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
/* helper modified by LLM (iteration 2): no changes */
// </vc-helpers>

// <vc-spec>
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): used i64 for exec computations to avoid int type in exec code */
{
    let nn: i64 = n as i64;
    let rr: i64 = r as i64;
    let k = if rr < nn - 1 { rr } else { nn - 1 };
    let tri = (k * (k + 1)) / 2;
    let extra = if rr >= nn { 1 } else { 0 };
    let res = tri + extra;
    res as i8
}
// </vc-code>


}

fn main() {}