use vstd::prelude::*;

verus! {

fn abs(x: i32) -> (result: i32)
    requires
        x != i32::MIN,
    ensures
        result >= 0,
        result == x || result == -x,
{
    return 0;  // TODO: Remove this line and implement the function body
}

fn main() {}
}
