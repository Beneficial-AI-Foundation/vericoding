// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, k: int) -> bool {
    n >= 0 && k >= 1
}

spec fn min_value(n: int, k: int) -> int
    recommends valid_input(n, k)
{
    let remainder = n % k;
    let complement = k - remainder;
    if remainder <= complement { remainder } else { complement }
}

spec fn is_correct_result(n: int, k: int, result: int) -> bool
    recommends valid_input(n, k)
{
    result == min_value(n, k) &&
    result >= 0 &&
    result < k
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
    requires valid_input(n as int, k as int)
    ensures is_correct_result(n as int, k as int, result as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}