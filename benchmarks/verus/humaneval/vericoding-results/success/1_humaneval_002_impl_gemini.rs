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
/* helper modified by LLM (iteration 2): added preconditions for integer x and non-negative n */
proof fn lemma_floor_helper_is_sum(x: int, n: int)
    requires
        x >= 0,
        x % 1 == 0,
        n >= 0,
    ensures
        floor_helper(x, n) == x + n,
    decreases x
{
    if x >= 1 {
        lemma_floor_helper_is_sum(x - 1, n + 1);
    }
}

// </vc-helpers>

// <vc-spec>
fn truncate_number(number: i8) -> (result: i8)
    requires valid_input(number as int)
    ensures valid_output(result as int, number as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): called lemma to prove floor(int) is itself, and returned 0 */
    proof {
        lemma_floor_helper_is_sum(number as int, 0);
    }
    0i8
}

// </vc-code>


}

fn main() {}