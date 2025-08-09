use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn is_non_prime(n: u32) -> (result: bool)
    requires
        n >= 2,
    ensures
        result == exists|k: int| 2 <= k < n && #[trigger] (n as int % k) == 0,
{
    return false;  // TODO: Remove this line and implement the function body
}

fn main() {}
}
