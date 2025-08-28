use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn has_divisor_in_range(n: int, start: int, end: int) -> bool {
    exists|k: int| start <= k < end && #[trigger] (n % k) == 0
}

proof fn divisor_range_split(n: int, start: int, mid: int, end: int)
    requires start <= mid <= end
    ensures has_divisor_in_range(n, start, end) == 
            (has_divisor_in_range(n, start, mid) || has_divisor_in_range(n, mid, end))
{
}

proof fn divisor_found_implies_exists(n: int, k: int)
    requires 2 <= k < n && n % k == 0
    ensures has_divisor_in_range(n, 2, n)
{
    assert(has_divisor_in_range(n, 2, n)) by {
        assert(2 <= k < n && n % k == 0);
    }
}

proof fn no_divisor_implies_not_exists(n: int, upper: int)
    requires 2 <= upper <= n,
        (forall|k: int| 2 <= k < upper ==> n % k != 0)
    ensures !has_divisor_in_range(n, 2, upper)
{
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
    let mut i = 2;
    while i < n
        invariant
            2 <= i <= n,
            forall|k: int| 2 <= k < i ==> (n as int % k) != 0,
        decreases n - i
    {
        if n % i == 0 {
            proof {
                divisor_found_implies_exists(n as int, i as int);
            }
            return true;
        }
        i += 1;
    }
    
    proof {
        no_divisor_implies_not_exists(n as int, n as int);
        assert(forall|k: int| 2 <= k < n ==> (n as int % k) != 0);
    }
    false
}
// </vc-code>

fn main() {}
}