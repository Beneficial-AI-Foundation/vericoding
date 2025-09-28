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
fn max_of_three_impl(a1: i8, a2: i8, a3: i8) -> (result: i8)
    requires
        valid_input(a1 as int, a2 as int, a3 as int)
    ensures
        result as int == max_of_three(a1 as int, a2 as int, a3 as int)
{
    if a1 >= a2 && a1 >= a3 {
        a1
    } else if a2 >= a3 {
        a2
    } else {
        a3
    }
}

fn min_of_three_impl(a1: i8, a2: i8, a3: i8) -> (result: i8)
    requires
        valid_input(a1 as int, a2 as int, a3 as int)
    ensures
        result as int == min_of_three(a1 as int, a2 as int, a3 as int)
{
    if a1 <= a2 && a1 <= a3 {
        a1
    } else if a2 <= a3 {
        a2
    } else {
        a3
    }
}
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
{
    let max_val = max_of_three_impl(a1, a2, a3);
    let min_val = min_of_three_impl(a1, a2, a3);
    max_val - min_val
}
// </vc-code>


}

fn main() {}