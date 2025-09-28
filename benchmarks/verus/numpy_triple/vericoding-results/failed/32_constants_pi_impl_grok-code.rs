// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helpers needed */
// </vc-helpers>

// <vc-spec>
fn pi() -> (result: i32)
    ensures
        result > 3 && result < 4
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): calculating pi approximation as 22/7 and casting to i32 */
    return ((22.0 / 7.0) as i32);
}
// </vc-code>


}
fn main() {}