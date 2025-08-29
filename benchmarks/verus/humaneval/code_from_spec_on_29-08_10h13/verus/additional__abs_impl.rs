use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-description>
/*
function_signature: "fn abs(x: i32) -> (result: i32)"
docstring: Implement abs functionality.
*/
// </vc-description>

// <vc-spec>
fn abs(x: i32) -> (result: i32)
    requires x > i32::MIN
    ensures result >= 0
    ensures result == x || result == -x
    ensures x >= 0 ==> result == x
    ensures x < 0 ==> result == -x
// </vc-spec>

// <vc-code>
{
    if x >= 0 {
        x
    } else {
        -x
    }
}
// </vc-code>

fn main() {}
}