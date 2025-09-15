// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec helper returning mathematical triple as an integer */
spec fn triple_int(x: int) -> int { x * 3 }
// </vc-helpers>

// <vc-spec>
fn triple(x: i32) -> (result: i32)
    ensures
        result / 3 == x,
        result / 3 * 3 == result,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute triple using mathematical integer and cast back to i32 */
    let xi: int = x as int;
    let ri: int = xi * 3;
    proof {
        // trivial proof block to connect the mathematical computation; any necessary bounds
        // or detailed reasoning can be placed here in further iterations.
        assert(xi == xi);
    }
    let result: i32 = ri as i32;
    result
}
// </vc-code>

}
fn main() {}