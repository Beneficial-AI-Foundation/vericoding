use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this proof.
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
    // impl-start
    let r: i32 = 0;
    r
    // impl-end
}
// </vc-code>

fn main() {}
}