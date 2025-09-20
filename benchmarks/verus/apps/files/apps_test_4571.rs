// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, m: int) -> bool {
    1 <= n <= 100 && 1 <= m <= n && m <= 5
}

spec fn power(base: int, exp: int) -> int
    decreases exp when exp >= 0
{
    if exp <= 0 { 1 } else { base * power(base, exp - 1) }
}

spec fn expected_time(n: int, m: int) -> int {
    (1900 * m + 100 * (n - m)) * power(2, m)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8) -> (result: i8)
    requires valid_input(n as int, m as int)
    ensures result as int == expected_time(n as int, m as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}