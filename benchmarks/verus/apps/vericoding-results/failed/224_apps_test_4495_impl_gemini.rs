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
/* helper modified by LLM (iteration 4): used correct vstd lemma 'lemma_div_is_ordered' */
proof fn lemma_count_is_nonnegative(a: int, b: int, x: int)
    requires valid_input(a, b, x)
    ensures count_divisible_in_range(a, b, x) >= 0
{
    if a > 0 {
        // From valid_input, we have a <= b and x > 0.
        // We want to prove b/x - (a-1)/x >= 0, which is b/x >= (a-1)/x.
        vstd::arithmetic::div_mod::lemma_div_is_ordered(x, a - 1, b);
    }
    // If a == 0, count_divisible_in_range is (b/x) + 1.
    // Since b >= 0 and x > 0, b/x >= 0. So (b/x) + 1 >= 1.
    // This is proven automatically by the SMT solver.
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
    /* code modified by LLM (iteration 4): implementation is correct, relies on fixed helper */
    let count = if a == 0 {
        b / x + 1
    } else {
        b / x - (a - 1) / x
    };

    proof {
        lemma_count_is_nonnegative(a as int, b as int, x as int);
    }

    count
}

// </vc-code>


}

fn main() {}