// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int, k: int, m: int, d: int) -> bool {
    2 <= n && 2 <= k <= n && 1 <= m <= n && 1 <= d <= n && m * d * k >= n
}

spec fn candies_used(x: int, d: int, k: int) -> int {
    x * ((d - 1) * k + 1)
}

spec fn valid_distribution(x: int, d: int, n: int, k: int, m: int, d_max: int) -> bool {
    1 <= x <= m && 1 <= d <= d_max && candies_used(x, d, k) <= n
}

spec fn person1_candies(x: int, d: int) -> int {
    x * d
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, k: int, m: int, d: int) -> (result: int)
    requires valid_input(n, k, m, d)
    ensures
        result >= 0 &&
        result <= m * d &&
        (forall|x: int, d_val: int| valid_distribution(x, d_val, n, k, m, d) ==> person1_candies(x, d_val) <= result) &&
        (exists|x: int, d_val: int| valid_distribution(x, d_val, n, k, m, d) && person1_candies(x, d_val) == result)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}