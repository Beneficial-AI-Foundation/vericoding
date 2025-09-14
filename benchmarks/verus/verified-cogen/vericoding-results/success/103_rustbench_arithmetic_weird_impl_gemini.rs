// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn arithmetic_weird() -> (result: i32)
    ensures
        result < 10
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to prove loop termination */
    let mut result: i32 = 0;
    while result < 9
        invariant result <= 9
        decreases 9 - result
    {
        result = result + 1;
    }
    result
}
// </vc-code>

}
fn main() {}