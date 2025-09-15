// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed bounds and lemma to handle i32 overflow correctly */
proof fn triple_properties(x: i32)
    requires x >= -715827882 && x <= 715827882
    ensures
        (3 * x) / 3 == x,
        (3 * x) / 3 * 3 == 3 * x,
{
    let result = 3 * x;
    assert(result >= -2147483646 && result <= 2147483646);
    assert(result / 3 == x);
    assert(result / 3 * 3 == result);
}
// </vc-helpers>

// <vc-spec>
fn triple(x: i32) -> (result: i32)
    ensures
        result / 3 == x,
        result / 3 * 3 == result,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed syntax error by removing misplaced requires clause */
    let result = 3 * x;
    proof {
        triple_properties(x);
    }
    result
}
// </vc-code>

}
fn main() {}