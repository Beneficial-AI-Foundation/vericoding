use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn arithmetic_weird() -> (result: i32)
    ensures
        result < 10
{
    return 0;  // TODO: Remove this line and implement the function body
}

fn main() {}
}
