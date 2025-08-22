use vstd::prelude::*;

verus! {

fn abs(x: i32) -> (result: i32)
    /* code modified by LLM (iteration 2): moved requires clause before ensures clause to fix syntax error */
    requires x > i32::MIN,
    ensures
        result >= 0,
        result == x || result == -x,
{
    if x >= 0 {
        x
    } else {
        /* code modified by LLM (iteration 2): negation is now safe due to precondition */
        -x
    }
}

fn main() {}
}