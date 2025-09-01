use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn arithmetic_weird() -> (result: i32)
    // post-conditions-start
    ensures
        result < 10
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut x: i32 = 0;
    x = x + 2;
    x = x + 3;
    x = x + 4;
    assert(x == 9); 
    x
    // impl-end
}
// </vc-code>

fn main() {}
}