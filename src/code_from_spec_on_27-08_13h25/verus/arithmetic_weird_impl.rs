use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn arithmetic_weird() -> (result: i32)
    // post-conditions-start
    ensures
        result < 10
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    5
}
// </vc-code>

fn main() {}
}