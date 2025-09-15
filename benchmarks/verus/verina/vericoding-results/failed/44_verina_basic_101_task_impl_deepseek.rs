// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Fixed old() usage and simplified proof */
spec fn triple_spec(x: int) -> int {
    x * 3
}

proof fn triple_div_proof(x: int)
    ensures
        triple_spec(x) / 3 == x,
        triple_spec(x) % 3 == 0,
{
    assert(triple_spec(x) == x * 3);
    assert(x * 3 / 3 == x);
    assert((x * 3) % 3 == 0);
}
// </vc-helpers>

// <vc-spec>
fn triple(x: i32) -> (result: i32)
    ensures
        result / 3 == x,
        result / 3 * 3 == result,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed compilation errors and simplified implementation */ {
    let result = x * 3;
    proof {
        triple_div_proof(x as int);
    }
    result
}
// </vc-code>

}
fn main() {}