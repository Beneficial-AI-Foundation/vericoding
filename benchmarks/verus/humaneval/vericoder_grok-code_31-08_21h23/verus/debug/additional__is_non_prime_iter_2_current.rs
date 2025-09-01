use vstd::prelude::*;

verus! {

// <vc-helpers>
use vstd::prelude::*;
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
            2 <= (i as int) <= (n as int),
            forall |j: int| 2 <= j < (i as int) ==> #[trigger] ((n as int) % j) != 0,
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