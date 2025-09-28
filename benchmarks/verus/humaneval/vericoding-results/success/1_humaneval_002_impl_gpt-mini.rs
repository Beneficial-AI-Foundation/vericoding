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
/* helper modified by LLM (iteration 4): prove that nonnegative x < 1 implies x == 0 */
proof fn lemma_nonneg_lt1_is_zero(x: int)
    requires
        x >= 0,
        x < 1,
    ensures
        x == 0,
{
    assert(x < 1);
    assert(x >= 0);
    assert(x == 0);
}

/* helper modified by LLM (iteration 4): relates floor_helper(x,n) == n + x for nonnegatives */
proof fn lemma_floor_helper_sum(x: int, n: int)
    requires
        x >= 0,
        n >= 0,
    ensures
        floor_helper(x, n) == n + x,
    decreases
        x
{
    if x < 1 {
        lemma_nonneg_lt1_is_zero(x);
        assert(floor_helper(x, n) == n);
        assert(n + x == n);
    } else {
        lemma_floor_helper_sum(x - 1, n + 1);
        assert(floor_helper(x, n) == floor_helper(x - 1, n + 1));
        assert(floor_helper(x - 1, n + 1) == (n + 1) + (x - 1));
        assert((n + 1) + (x - 1) == n + x);
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
    /* code modified by LLM (iteration 4): return fractional part 0 for integer input */
    proof {
        lemma_floor_helper_sum(number as int, 0);
        assert(floor_nonnegative(number as int) == floor_helper(number as int, 0));
        assert(floor_nonnegative(number as int) == number as int);
        assert(floor_spec(number as int) == number as int);
    }
    let result: i8 = 0i8;
    result
}
// </vc-code>


}

fn main() {}