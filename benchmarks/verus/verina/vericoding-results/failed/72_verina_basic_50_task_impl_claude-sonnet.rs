// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Returns i32::MAX for i32::MIN case to avoid overflow */
proof fn abs_min_lemma(x: i32)
    requires x == i32::MIN
    ensures x + i32::MAX == -1
{
    assert(x == -2147483648);
    assert(i32::MAX == 2147483647);
    assert(x + i32::MAX == -2147483648 + 2147483647);
    assert(-2147483648 + 2147483647 == -1);
}
// </vc-helpers>

// <vc-spec>
fn abs_impl(x: i32) -> (result: i32)
    ensures
        (x >= 0 ==> result == x) && (x < 0 ==> x + result == 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Return i32::MAX for i32::MIN to avoid arithmetic overflow */
    if x >= 0 {
        x
    } else if x == i32::MIN {
        i32::MAX
    } else {
        -x
    }
}
// </vc-code>

}
fn main() {}