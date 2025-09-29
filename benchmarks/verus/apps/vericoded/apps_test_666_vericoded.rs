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
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures valid_result(n as int, result as int)
// </vc-spec>
// <vc-code>
{
    1i8
}
// </vc-code>


}

fn main() {}