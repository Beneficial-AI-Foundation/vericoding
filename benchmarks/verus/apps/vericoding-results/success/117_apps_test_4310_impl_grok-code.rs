// <vc-preamble>
use vstd::prelude::*;

verus! {
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
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(a1: i8, a2: i8, a3: i8) -> (result: i8)
    requires 
        valid_input(a1 as int, a2 as int, a3 as int)
    ensures 
        result as int >= 0,
        result as int == minimum_cost(a1 as int, a2 as int, a3 as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Compute the maximum and minimum values inline without helper functions, then subtract to get the cost. */
{
    let mut max_val = a1;
    if a2 > max_val {
        max_val = a2;
    }
    if a3 > max_val {
        max_val = a3;
    }
    let mut min_val = a1;
    if a2 < min_val {
        min_val = a2;
    }
    if a3 < min_val {
        min_val = a3;
    }
    max_val - min_val
}
// </vc-code>


}

fn main() {}