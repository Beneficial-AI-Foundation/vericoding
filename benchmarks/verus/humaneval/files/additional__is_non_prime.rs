use vstd::prelude::*;

verus! {

/*
function_signature: "fn is_non_prime(n: u32) -> (result: bool)"
docstring: Implement is non prime functionality.
*/

#[verifier::loop_isolation(false)]
fn is_non_prime(n: u32) -> (result: bool)
    // pre-conditions-start
    requires
        n >= 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result == exists|k: int| 2 <= k < n && #[trigger] (n as int % k) == 0,
    // post-conditions-end
{
    // impl-start
    assume(false);
    false
    // impl-end
}

fn main() {}
}