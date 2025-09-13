// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn triangular_number(m: int) -> int
    recommends m >= 0
{
    m * (m + 1) / 2
}

spec fn valid_input(n: int) -> bool
{
    n >= 1
}

spec fn valid_result(n: int, result: int) -> bool
    recommends valid_input(n)
{
    result >= 1 && result <= n
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