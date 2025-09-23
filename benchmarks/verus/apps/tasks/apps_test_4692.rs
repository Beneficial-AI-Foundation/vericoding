// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(m: int) -> bool {
    1 <= m <= 23
}

spec fn hours_until_new_year(m: int) -> int
    recommends valid_input(m)
{
    48 - m
}

spec fn valid_output(m: int, result: int) -> bool
    recommends valid_input(m)
{
    result == hours_until_new_year(m) && 25 <= result <= 47
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(m: i8) -> (result: i8)
    requires valid_input(m as int)
    ensures valid_output(m as int, result as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}