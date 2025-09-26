// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(number: int) -> bool {
    number >= 0
}

spec fn valid_output(result: int, input: int) -> bool {
    0 <= result < 1 && result == input - floor_spec(input)
}

spec fn floor_spec(x: int) -> int {
    if x >= 0 {
        floor_nonnegative(x)
    } else {
        -ceil_nonnegative(-x)
    }
}

spec fn floor_nonnegative(x: int) -> int {
    floor_helper(x, 0)
}

spec fn floor_helper(x: int, n: int) -> int 
    decreases x when x >= 0 && n >= 0
{
    if x < 1 { 
        n
    } else { 
        floor_helper(x - 1, n + 1)
    }
}

spec fn ceil_nonnegative(x: int) -> int {
    if x == 0 { 
        0
    } else if floor_nonnegative(x) == x {
        x
    } else {
        floor_nonnegative(x) + 1
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn truncate_number(number: i8) -> (result: i8)
    requires valid_input(number as int)
    ensures valid_output(result as int, number as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}