use vstd::prelude::*;

verus! {

// <vc-helpers>
fn has_divisor(n: u32, start: u32, end: u32) -> (result: bool)
    requires
        2 <= start,
        start <= end,
        end <= n,
    ensures
        result == exists|k: int| start <= k < end && #[trigger] (n as int % k) == 0,
    decreases end - start,
{
    if start >= end {
        return false;
    }
    if n % start == 0 {
        return true;
    }
    has_divisor(n, start + 1, end)
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
    has_divisor(n, 2, n)
}
// </vc-code>

fn main() {}
}