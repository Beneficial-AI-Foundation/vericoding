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
    let mut k = 2;
    while k < n {
        invariant (2 <= k && (forall | i: u32 | 2 <= i && i < k ==> #[trigger] (n % i) != 0));
        if n % k == 0 {
            return true;
        }
        k += 1;
    }
    return false;
}
// </vc-code>

fn main() {}
}