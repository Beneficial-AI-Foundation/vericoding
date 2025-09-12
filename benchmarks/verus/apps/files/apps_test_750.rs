// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, k: int) -> bool {
    n >= 1 && k >= 1
}

spec fn sheets_needed(n: int) -> (int, int, int) {
    (2 * n, 5 * n, 8 * n)
}

spec fn total_sheets_needed(n: int) -> int {
    2 * n + 5 * n + 8 * n
}

spec fn ceil_div(a: int, b: int) -> int
    recommends b > 0
{
    (a + b - 1) / b
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, k: int) -> (result: int)
    requires 
        valid_input(n, k)
    ensures 
        result == ceil_div(2 * n, k) + ceil_div(5 * n, k) + ceil_div(8 * n, k),
        result >= 0,
        result >= (total_sheets_needed(n) + k - 1) / k
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}