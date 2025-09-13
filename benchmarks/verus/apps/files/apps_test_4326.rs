// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int) -> bool {
    1 <= n <= 1000
}

spec fn max_groups_with_at_least_three(n: int) -> int
    requires valid_input(n)
{
    n / 3
}

spec fn valid_solution(n: int, result: int) -> bool
    requires valid_input(n)
{
    (result == max_groups_with_at_least_three(n)) &&
    (result >= 0) &&
    (result <= n)
}
// </vc-helpers>

// <vc-spec>
// </vc-spec>
// <vc-code>
{
  assume(false);
  unreached()
}
// </vc-code>


}

fn main() {}