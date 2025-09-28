// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int) -> bool {
    a > 1 && b >= 0
}

spec fn sockets_after_strips(strips: int, a: int) -> int
    recommends a > 1 && strips >= 0
{
    1 + strips * (a - 1)
}

spec fn ceiling_division(x: int, y: int) -> int
    recommends y > 0
{
    if x % y == 0 {
        x / y
    } else if x >= 0 {
        x / y + 1
    } else {
        x / y
    }
}

spec fn min_strips_needed(a: int, b: int) -> int
    recommends valid_input(a, b)
{
    if b <= 1 {
        0
    } else {
        ceiling_division(b - 1, a - 1)
    }
}

spec fn correct_result(a: int, b: int, result: int) -> bool
    recommends valid_input(a, b)
{
    result >= 0 &&
    sockets_after_strips(result, a) >= b &&
    (result == 0 || sockets_after_strips(result - 1, a) < b)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix proof block placement and ensure proper verification */
proof fn lemma_sockets_after_strips_monotonic(strips1: int, strips2: int, a: int)
    requires
        a > 1,
        strips1 >= 0,
        strips2 >= 0,
        strips1 <= strips2
    ensures
        sockets_after_strips(strips1, a) <= sockets_after_strips(strips2, a)
    decreases strips2 - strips1
{
    if strips1 < strips2 {
        assert(sockets_after_strips(strips1 + 1, a) == sockets_after_strips(strips1, a) + (a - 1));
        lemma_sockets_after_strips_monotonic(strips1 + 1, strips2, a);
    }
}

proof fn lemma_ceiling_division_properties(x: int, y: int)
    requires
        y > 0,
        x >= 0
    ensures
        ceiling_division(x, y) >= x / y,
        ceiling_division(x, y) * y >= x
{
    if x % y == 0 {
        assert(ceiling_division(x, y) * y == x);
    } else {
        assert(ceiling_division(x, y) == x / y + 1);
        assert(ceiling_division(x, y) * y >= x);
    }
}

proof fn lemma_min_strips_correctness(a: int, b: int)
    requires
        a > 1,
        b >= 0
    ensures
        correct_result(a as int, b as int, min_strips_needed(a, b) as int)
    decreases b
{
    if b <= 1 {
        assert(sockets_after_strips(0, a) == 1);
    } else {
        let strips = min_strips_needed(a, b);
        let cd = ceiling_division(b - 1, a - 1);
        assert(strips == cd);
        assert(strips >= 0);
        assert(sockets_after_strips(strips, a) >= b);
        
        if strips > 0 {
            lemma_ceiling_division_properties(b - 1, a - 1);
            assert(sockets_after_strips(strips - 1, a) < b);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: i8)
    requires valid_input(a as int, b as int)
    ensures correct_result(a as int, b as int, result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix implementation with proper casting and verification */
{
    proof {
        lemma_min_strips_correctness(a as int, b as int);
    }
    
    if b <= 1 {
        0
    } else {
        let numerator = (b as i32) - 1;
        let denominator = (a as i32) - 1;
        let remainder = numerator % denominator;
        let strips_needed = if remainder == 0 {
            numerator / denominator
        } else {
            numerator / denominator + 1
        };
        proof {
            assert(strips_needed as int == min_strips_needed(a as int, b as int));
        }
        strips_needed as i8
    }
}
// </vc-code>


}

fn main() {}