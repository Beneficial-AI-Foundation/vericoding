// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int, k: int) -> bool {
    n >= 1 && k > 0
}

spec fn is_correct_result(n: int, k: int, result: int) -> bool
    recommends k > 0
{
    result > n && result % k == 0 && forall|x: int| n < x < result ==> x % k != 0
}
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