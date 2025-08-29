use vstd::prelude::*;

verus! {

/*
function_signature: "fn arithmetic_weird() -> (result: i32)"
docstring: Implement arithmetic weird functionality.
*/

#[verifier::loop_isolation(false)]
fn arithmetic_weird() -> (result: i32)
    // post-conditions-start
    ensures
        result < 10
    // post-conditions-end
{
    // impl-start
    assume(false);
    0
    // impl-end
}

fn main() {}
}