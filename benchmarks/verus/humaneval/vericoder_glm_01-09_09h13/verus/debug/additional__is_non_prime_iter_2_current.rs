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
    let mut i: u32 = 2;
    while i < n
        invariant
            2 <= i <= n,
            forall |j: u32| 2 <= j < i ==> n % j != 0,
        decreases n - i,
    {
        if n % i == 0 {
            return true;
        }
        i += 1;
    }
    false
}
// </vc-code>

fn main() {}
}