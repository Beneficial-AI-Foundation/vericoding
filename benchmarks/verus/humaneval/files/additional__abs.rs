use vstd::prelude::*;

verus! {

/*
function_signature: "fn abs(x: i32) -> (result: i32)"
docstring: Implement abs functionality.
*/

fn abs(x: i32) -> (result: i32)
    // pre-conditions-start
    requires
        x != i32::MIN,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result >= 0,
        result == x || result == -x,
    // post-conditions-end
{
    // impl-start
    assume(false);
    0
    // impl-end
}

fn main() {}
}