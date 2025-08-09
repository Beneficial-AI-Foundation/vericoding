use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn arithmetic() -> (result: i32)
    ensures
        result < 10
{
    0
}

fn main() {}
}