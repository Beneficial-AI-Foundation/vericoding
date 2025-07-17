use vstd::prelude::*;

verus! {

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
    return 0;  // TODO: Remove this line and implement the function body
}

fn main() {}
}
