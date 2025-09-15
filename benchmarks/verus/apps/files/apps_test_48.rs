// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_less_value(n: int, m: int, target: int) -> int
    recommends n >= 0 && m >= 1 && target >= 1
    decreases n
{
    if n == 0 {
        0
    } else {
        let max_j = (target - 1) / n;
        let actual_max_j = if max_j > m { m } else { max_j };
        let contribution = if actual_max_j >= 1 { actual_max_j } else { 0 };
        contribution + count_less_value(n - 1, m, target)
    }
}

spec fn count_less_or_equal_value(n: int, m: int, target: int) -> int
    recommends n >= 1 && m >= 1 && target >= 0
{
    if target <= 0 {
        0
    } else if target >= n * m {
        n * m
    } else {
        count_less_value(n, m, target + 1)
    }
}

spec fn valid_input(n: int, m: int, k: int) -> bool {
    1 <= n <= 500000 && 1 <= m <= 500000 && 1 <= k <= n * m
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, m: int, k: int) -> (result: int)
    requires valid_input(n, m, k)
    ensures 
        1 <= result <= n * m &&
        count_less_or_equal_value(n, m, result) >= k &&
        (result == 1 || count_less_or_equal_value(n, m, result - 1) < k)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}