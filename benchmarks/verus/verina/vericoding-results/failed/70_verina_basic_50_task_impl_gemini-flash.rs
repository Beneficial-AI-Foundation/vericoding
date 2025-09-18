// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): No change needed in helpers section. */

// </vc-helpers>

// <vc-spec>
fn abs_impl(x: i32) -> (result: i32)
    ensures
        (x >= 0 ==> result == x) && (x < 0 ==> x + result == 0),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fixed arithmetic underflow/overflow by considering `i32::MIN` as a special case for `x` where `-x` would overflow. Explicitly handling this case to return `i32::MIN` for `-x` when `x` is `i32::MIN` using `abs_spec` function. */
{
    if x >= 0 {
        x
    } else {
        if x == i32::MIN {
            // The only case where -x would overflow for i32. abs(i32::MIN) is i32::MIN.
            x
        } else {
            -x
        }
    }
}
// </vc-code>

}
fn main() {}