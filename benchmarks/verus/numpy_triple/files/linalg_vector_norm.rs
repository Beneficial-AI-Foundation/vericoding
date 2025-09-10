use vstd::prelude::*;

verus! {

fn vector_norm(x: Vec<i32>, p: i32) -> (result: i32)
    requires p >= 0,
    ensures 
        result >= 0,
        x@.len() == 0 ==> result == 0,
        result >= 0
{
    assume(false);
    unreached()
}

}
fn main() {}