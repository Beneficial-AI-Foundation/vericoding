// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compute triple as i32 */
spec fn mul3(x: i32) -> (r: i32)
    ensures
        r == x * 3i32,
{
    x * 3i32
}

/* helper modified by LLM (iteration 5): prove division properties for triple as i32 */
proof fn mul3_divides(x: i32, r: i32)
    requires
        r == x * 3i32,
    ensures
        r / 3i32 == x,
        r / 3i32 * 3i32 == r,
{
    proof {
        assert(r == x * 3i32);
        assert(r / 3i32 == x);
        assert(r / 3i32 * 3i32 == r);
    }
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
    /* code modified by LLM (iteration 5): compute triple and invoke proof helper */
    let result: i32 = x * 3i32;
    proof {
        mul3_divides(x, result);
    }
    result
}
// </vc-code>

}
fn main() {}