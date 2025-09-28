// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int, x: int) -> bool {
    a >= 0 && b >= a && x > 0
}

spec fn count_divisible_in_range(a: int, b: int, x: int) -> int
    recommends valid_input(a, b, x)
{
    if a == 0 {
        b / x + 1
    } else {
        b / x - (a - 1) / x
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed integer literal syntax from 0int to 0 */
fn lemma_division_bounds(a: int, b: int, x: int)
    requires
        valid_input(a, b, x),
        a <= 127,
        b <= 127,
        x >= 1,
    ensures
        count_divisible_in_range(a, b, x) >= 0,
        count_divisible_in_range(a, b, x) <= 127,
{
    if a == 0 {
        assert(b / x >= 0);
        assert(b / x + 1 >= 1);
        assert(b / x + 1 <= b + 1);
        assert(b + 1 <= 128);
    } else {
        assert(b / x >= 0);
        assert((a - 1) / x >= 0);
        assert(b / x - (a - 1) / x >= 0);
        assert(b / x - (a - 1) / x <= b);
    }
}
// </vc-helpers>

// <vc-spec>
fn count_divisible(a: i8, b: i8, x: i8) -> (count: i8)
    requires 
        valid_input(a as int, b as int, x as int),
    ensures 
        count as int == count_divisible_in_range(a as int, b as int, x as int),
        count >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed integer literal comparison by using 0 instead of 0int */
    proof {
        lemma_division_bounds(a as int, b as int, x as int);
    }
    
    let result = if a == 0i8 {
        (b / x) + 1
    } else {
        (b / x) - ((a - 1) / x)
    };
    
    assert(result as int == count_divisible_in_range(a as int, b as int, x as int));
    assert(result >= 0);
    
    result
}
// </vc-code>


}

fn main() {}