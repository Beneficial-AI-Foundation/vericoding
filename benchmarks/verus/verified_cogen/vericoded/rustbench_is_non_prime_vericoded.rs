// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn has_divisor_below(n: int, bound: int) -> bool { exists|k: int| 2 <= k < bound && #[trigger] (n % k) == 0 }

spec fn is_composite_int(n: int) -> bool { exists|k: int| 2 <= k < n && #[trigger] (n % k) == 0 }
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn is_non_prime(n: u32) -> (result: bool)
    requires
        n >= 2,
    ensures
        result == exists|k: int| 2 <= k < n && #[trigger] (n as int % k) == 0,
// </vc-spec>
// <vc-code>
{
    let mut k: u32 = 2;
    let mut found: bool = false;
    while k < n
        invariant
            2 <= k as int && k as int <= n as int,
            found == exists|j: int| 2 <= j < k as int && #[trigger] ((n as int) % j) == 0,
        decreases (n - k) as int
    {
        if n % k == 0 {
            proof {
                assert(((n as int) % (k as int)) == 0);
            }
            found = true;
        }
        k = k + 1;
    }
    proof { assert(k as int == n as int); }
    found
}
// </vc-code>

}
fn main() {}