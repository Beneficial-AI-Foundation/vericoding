// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int, c: int, d: int) -> bool {
    1 <= a <= 10000 && 1 <= b <= 10000 && 1 <= c <= 10000 && 1 <= d <= 10000
}

spec fn max_area(a: int, b: int, c: int, d: int) -> int {
    if a * b >= c * d { a * b } else { c * d }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_multiplication_bounds(x: int, y: int)
    requires
        1 <= x <= 10000,
        1 <= y <= 10000
    ensures
        x * y >= 1,
        x * y <= 100000000
{
    assert(x * y >= 1) by {
        assert(1 <= x);
        assert(1 <= y);
    };
    assert(x * y <= 100000000) by {
        assert(x <= 10000);
        assert(y <= 10000);
    };
}

proof fn lemma_max_area_properties(a: int, b: int, c: int, d: int)
    requires
        valid_input(a, b, c, d)
    ensures
        max_area(a, b, c, d) >= a * b,
        max_area(a, b, c, d) >= c * d,
        max_area(a, b, c, d) == a * b || max_area(a, b, c, d) == c * d
{
}

proof fn lemma_int_comparison(x: int, y: int)
    ensures
        x >= y || x < y
{
}
/* helper modified by LLM (iteration 5): Fixed proof syntax - replaced proof blocks with assert-by blocks */
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8, d: i8) -> (result: i8)
    requires 
        valid_input(a as int, b as int, c as int, d as int)
    ensures 
        result as int == max_area(a as int, b as int, c as int, d as int),
        result as int >= (a as int) * (b as int) && result as int >= (c as int) * (d as int),
        result as int == (a as int) * (b as int) || result as int == (c as int) * (d as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Direct comparison with proper casting */
    proof {
        lemma_max_area_properties(a as int, b as int, c as int, d as int);
    }
    
    if (a as i32) * (b as i32) >= (c as i32) * (d as i32) {
        a * b
    } else {
        c * d
    }
}
// </vc-code>


}

fn main() {}