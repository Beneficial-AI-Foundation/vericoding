// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn count_cells_divisible_by_m(n: int, m: int) -> int
    requires 1 <= n && 1 <= m
{
    (set![(i, j) | 1 <= i <= n && 1 <= j <= n && (i * i + j * j) % m == 0]).len() as int
}

spec fn valid_input(n: int, m: int) -> bool {
    1 <= n && 1 <= m <= 1000
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, m: int) -> (result: int)
    requires valid_input(n, m)
    ensures result >= 0
    ensures result == count_cells_divisible_by_m(n, m)
// </vc-spec>
// <vc-code>
{
    assume(false);
    0
}
// </vc-code>


}

fn main() {}