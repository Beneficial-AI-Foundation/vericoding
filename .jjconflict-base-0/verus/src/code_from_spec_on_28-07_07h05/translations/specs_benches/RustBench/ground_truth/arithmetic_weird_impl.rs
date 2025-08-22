use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn arithmetic_weird() -> (result: i32)
    ensures
        result < 10
{
    return 0;
}

fn main() {}
}