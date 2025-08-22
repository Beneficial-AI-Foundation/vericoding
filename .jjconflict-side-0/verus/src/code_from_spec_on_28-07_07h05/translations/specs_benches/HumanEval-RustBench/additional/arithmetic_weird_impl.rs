use vstd::prelude::*;

verus! {

//IMPL arithmetic_weird
#[verifier::loop_isolation(false)]
fn arithmetic_weird() -> (result: i32)
    // post-conditions-start
    ensures
        result < 10
    // post-conditions-end
{
    5
}

fn main() {}
}