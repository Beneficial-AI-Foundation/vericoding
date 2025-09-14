// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): lemma proving 0 < 10 */
proof fn zero_lt_10() ensures 0 < 10 { assert(0 < 10); }
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn arithmetic_weird() -> (result: i32)
    ensures
        result < 10
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): return 0 and prove result < 10 */
    let r: i32 = 0;
    proof {
        zero_lt_10();
        assert(r == 0);
        assert(r < 10);
    }
    r
}
// </vc-code>

}
fn main() {}