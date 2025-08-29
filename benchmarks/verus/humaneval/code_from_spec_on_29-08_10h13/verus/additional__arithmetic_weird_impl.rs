use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-description>
/*
function_signature: "fn arithmetic_weird() -> (result: i32)"
docstring: Implement arithmetic weird functionality.
*/
// </vc-description>

// <vc-spec>
fn arithmetic_weird() -> (result: i32)
    ensures result == 1
// </vc-spec>

// <vc-code>
{
    1
}
// </vc-code>

fn main() {}
}