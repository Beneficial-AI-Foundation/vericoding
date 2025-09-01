use vstd::prelude::*;

verus! {

// <vc-helpers>
// (No helpers needed for this implementation)
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
    let mut k: u32 = 2;
    let mut found: bool = false;
    while k < n
        invariant 2 <= k && k <= n;
        invariant found == exists|i: int| 2 <= i && i < (k as int) && #[trigger] (n as int % i) == 0;
        decreases (n - k);
    {
        if n % k == 0 {
            found = true;
            k = n;
        } else {
            k = k + 1;
        }
    }
    found
}
// </vc-code>

fn main() {}
}