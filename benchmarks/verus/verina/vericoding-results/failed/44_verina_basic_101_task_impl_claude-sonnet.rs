// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed unsupported abs() method */
proof fn triple_properties(x: i32)
    requires x >= -715827882 && x <= 715827882
    ensures 
        (x * 3) / 3 == x,
        (x * 3) / 3 * 3 == x * 3
{
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
    /* code modified by LLM (iteration 5): removed misplaced requires clause from method body */
    let result = x * 3;
    proof {
        triple_properties(x);
    }
    result
}
// </vc-code>

}
fn main() {}