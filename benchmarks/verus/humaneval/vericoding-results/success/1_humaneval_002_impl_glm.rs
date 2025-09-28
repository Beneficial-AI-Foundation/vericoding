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
/* helper modified by LLM (iteration 2): fixed lemma definition syntax */
proof fn floor_helper_property(x: int, n: int)
    requires x >= 0 && n >= 0
    ensures floor_helper(x, n) == n + x
    decreases x
{
    if x == 0 {
        assert(floor_helper(x, n) == n);
        assert(n == n + x);
    } else {
        assert(floor_helper(x, n) == floor_helper(x-1, n+1));
        floor_helper_property(x-1, n+1);
        assert(floor_helper(x-1, n+1) == (n+1) + (x-1));
        assert((n+1)+(x-1) == n+x);
    }
}

proof fn floor_nonnegative_identity(x: int)
    requires x >= 0
    ensures floor_nonnegative(x) == x
{
    reveal(floor_nonnegative);
    floor_helper_property(x,0);
    assert(floor_nonnegative(x) == floor_helper(x,0));
    assert(floor_helper(x,0) == 0+x == x);
}
// </vc-helpers>

// <vc-spec>
fn truncate_number(number: i8) -> (result: i8)
    requires valid_input(number as int)
    ensures valid_output(result as int, number as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed implementation to return fractional part */
{
    let result = 0;
    proof {
        reveal(floor_spec);
        floor_nonnegative_identity(number as int);
        assert(floor_spec(number as int) == floor_nonnegative(number as int));
        assert(floor_nonnegative(number as int) == (number as int));
        assert((number as int) - floor_spec(number as int) == 0);
    }
    result
}
// </vc-code>


}

fn main() {}