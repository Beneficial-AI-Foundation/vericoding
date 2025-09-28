// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers needed */
// </vc-helpers>

// <vc-spec>
fn triple(x: i32) -> (result: i32)
    ensures
        result / 3 == x,
        result / 3 * 3 == result,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Simplified implementation without requires clause in body */
    
    let result: i32 = x * 3;
    proof {
        assert(result == x * 3);
        assert(result / 3 == x);
        assert(result / 3 * 3 == result);
    }
    result
}
// </vc-code>

}
fn main() {}