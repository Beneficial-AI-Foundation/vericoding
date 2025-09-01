use vstd::prelude::*;

verus! {

// <vc-helpers>
// Provide a recursive helper that searches for a divisor starting from k.
fn has_divisor_from(n: u32, k: u32) -> (res: bool)
    requires
        n >= 2,
        2 <= k,
        k <= n,
    decreases (n - k)
    ensures
        res == exists|i: int| (k as int) <= i && i < n as int && #[trigger] (n as int % i) == 0,
{
    if k == n {
        false
    } else {
        if n % k == 0 {
            true
        } else {
            has_divisor_from(n, k + 1)
        }
    }
}
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
    // Call the helper starting from 2
    has_divisor_from(n, 2)
}
// </vc-code>

fn main() {}
}