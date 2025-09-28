// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): proof that true equals true */
proof fn helper_true_equality() {
    assert(true == true);
}

// </vc-helpers>

// <vc-spec>
fn true_() -> (result: bool)
    ensures 
        result == true,
        !result == false
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): set result to true and prove spec */
    let result = true;
    proof {
        helper_true_equality();
        assert(result == true);
        assert(!result == false);
    }
    result
}
// </vc-code>

}
fn main() {}