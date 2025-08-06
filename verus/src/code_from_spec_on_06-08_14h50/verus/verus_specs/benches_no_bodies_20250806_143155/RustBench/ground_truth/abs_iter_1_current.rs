use vstd::prelude::*;

verus! {

fn abs(x: i32) -> (result: i32)
    requires
        x != i32::MIN,
    ensures
        result >= 0,
        result == x || result == -x,
{
    if x < 0 {
        -x
    } else {
        x
    }
}

fn main() {}
}