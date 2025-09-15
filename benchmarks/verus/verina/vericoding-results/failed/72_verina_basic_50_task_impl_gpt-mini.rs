// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove properties of spec abs using cases */
proof fn abs_properties(x: int)
    ensures abs(x) >= 0 && (x >= 0 ==> abs(x) == x) && (x < 0 ==> x + abs(x) == 0)
{
    if x >= 0 {
        assert(abs(x) == x);
        assert(abs(x) >= 0);
    } else {
        assert(abs(x) == -x);
        assert(x + abs(x) == 0);
        assert(abs(x) >= 0);
    }
}
// </vc-helpers>

// <vc-spec>
fn abs_impl(x: i32) -> (result: i32)
    ensures
        (x >= 0 ==> result == x) && (x < 0 ==> x + result == 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute absolute value using native i32 conditional */
    if x >= 0 {
        x
    } else {
        -x
    }
}
// </vc-code>

}
fn main() {}