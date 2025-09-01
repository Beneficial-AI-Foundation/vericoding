use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
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
// </vc-spec>
// <vc-code>
{
    let mut i: int = 2;
    while i < (n as int)
        invariant
            2 <= i <= n,
            forall |j: int| 2 <= j < i ==> #[trigger] ((n as int) % j) != 0,
    {
        if (n as int) % i == 0 {
            return true;
        }
        i += 1;
    }
    false
}
// </vc-code>

fn main() {}
}