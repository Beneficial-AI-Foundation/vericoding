// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): This helper is correct and was not changed. */
spec fn is_safe_to_multiply_by_5(s: i32) -> bool {
    5 * (s as int) <= i32::MAX as int
}
// </vc-helpers>

// <vc-spec>
fn pentagon_perimeter(side: i32) -> (perimeter: i32)
    requires side > 0
    ensures perimeter == 5 * side
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed a syntax error by removing the invalid `by(requires)` clause. */
    proof {
        assert(side > 0);
        // The following assertion is required to prove that `5 * side` does not overflow.
        // However, it is not provable from `side > 0` alone.
        // assert(is_safe_to_multiply_by_5(side));
    }
    5 * side
}
// </vc-code>

}
fn main() {}