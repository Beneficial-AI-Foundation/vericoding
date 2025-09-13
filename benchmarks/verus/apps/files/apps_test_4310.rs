// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(a1: int, a2: int, a3: int) -> bool {
    1 <= a1 <= 100 && 1 <= a2 <= 100 && 1 <= a3 <= 100
}

spec fn max_of_three(a1: int, a2: int, a3: int) -> int {
    if a1 >= a2 && a1 >= a3 { a1 } else if a2 >= a3 { a2 } else { a3 }
}

spec fn min_of_three(a1: int, a2: int, a3: int) -> int {
    if a1 <= a2 && a1 <= a3 { a1 } else if a2 <= a3 { a2 } else { a3 }
}

spec fn minimum_cost(a1: int, a2: int, a3: int) -> int {
    max_of_three(a1, a2, a3) - min_of_three(a1, a2, a3)
}
// </vc-helpers>

// <vc-spec>
fn solve(a1: int, a2: int, a3: int) -> (result: int)
    requires 
        valid_input(a1, a2, a3)
    ensures 
        result >= 0,
        result == minimum_cost(a1, a2, a3)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}