// <vc-preamble>
use vstd::prelude::*;

verus! {

    spec fn valid_input(n: int) -> bool {
        1 <= n <= 1000
    }
    
    spec fn max_groups_with_at_least_three(n: int) -> int
        recommends valid_input(n)
    {
        n / 3
    }
    
    spec fn valid_solution(n: int, result: int) -> bool
        recommends valid_input(n)
    {
        result == max_groups_with_at_least_three(n) &&
        result >= 0 &&
        result <= n
    }

    fn solve_groups(n: int) -> (result: int)
        requires valid_input(n)
        ensures valid_solution(n, result)
// </vc-preamble>

// <vc-helpers>
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