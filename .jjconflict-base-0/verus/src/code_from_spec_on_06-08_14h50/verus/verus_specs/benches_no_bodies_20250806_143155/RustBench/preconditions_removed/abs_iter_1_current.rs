use vstd::prelude::*;

verus! {

fn abs(x: i32) -> (result: i32)
    ensures
        result >= 0,
        result == x || result == -x,
{
    if x >= 0 {
        x
    } else if x == i32::MIN {
        i32::MAX
    } else {
        -x
    }
}

fn main() {}
}