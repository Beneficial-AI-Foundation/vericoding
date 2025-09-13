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
fn solve(n: int, k: int) -> (result: int)
    requires valid_input(n, k)
    ensures is_correct_result(n, k, result)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}