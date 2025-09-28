// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed lemma_math_sub_add_i32 to use proper lemma for subtraction */
proof fn lemma_math_sub_add_i32(a: i32, b: i32)
    requires
        a >= b,
    ensures
        (a - b) + b == a,
{
    proof {
        // Basic mathematical property of integers
        assert(a - b + b == a) by {
            assert(a >= b);
        };
    }
}

proof fn lemma_math_add_sub_i32(a: i32, b: i32)
    ensures
        a + b - b == a,
{
    proof {
        // Basic mathematical property of integers
        assert(a + b - b == a) by {
            assert(true);
        };
    }
}
// </vc-helpers>

// <vc-spec>
fn multiple_returns(x: i32, y: i32) -> (result: (i32, i32))
    ensures
        result.0 == x + y,
        result.1 + y == x,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Simplified implementation with proper verification */
    let sum = x + y;
    let diff = x - y;
    proof {
        lemma_math_sub_add_i32(x, y);
        assert(diff + y == x);
        assert(sum == x + y);
    }
    (sum, diff)
}
// </vc-code>

}
fn main() {}