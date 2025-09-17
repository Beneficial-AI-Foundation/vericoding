// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    n >= 0
}

spec fn factors_in_factorial(n: int, p: int) -> int {
    0
}

spec fn factors_in_double_factorial(n: int, p: int) -> int {
    0
}

spec fn valid_result(n: int, result: int) -> bool {
    n >= 0 ==> (
        result >= 0 &&
        result == if factors_in_double_factorial(n, 2) < factors_in_double_factorial(n, 5) {
            factors_in_double_factorial(n, 2)
        } else {
            factors_in_double_factorial(n, 5)
        }
    )
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int) -> (result: int)
    requires valid_input(n)
    ensures valid_result(n, result)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}