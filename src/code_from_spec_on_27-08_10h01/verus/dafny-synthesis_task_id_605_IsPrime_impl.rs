use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn has_divisor_in_range(n: int, start: int, end: int) -> bool {
    exists|k: int| start <= k < end && n % k == 0
}

proof fn divisor_transitivity(n: int, mid: int, end: int)
    requires n >= 2, 2 <= mid <= end
    ensures has_divisor_in_range(n, 2, end) <==> (has_divisor_in_range(n, 2, mid) || has_divisor_in_range(n, mid, end))
{
}

proof fn no_divisor_means_prime(n: int, k: int)
    requires n >= 2, 2 <= k < n, !has_divisor_in_range(n, 2, k + 1)
    ensures n % k != 0
{
    if n % k == 0 {
        assert(has_divisor_in_range(n, 2, k + 1));
        assert(false);
    }
}

proof fn divisor_found_means_not_prime(n: int, k: int)
    requires n >= 2, 2 <= k < n, n % k == 0
    ensures has_divisor_in_range(n, 2, n)
{
    assert(has_divisor_in_range(n, 2, n));
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn is_prime(n: int) -> (result: bool)
    requires n >= 2
    ensures result <==> (forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut i = 2;
    while i < n
        invariant 2 <= i <= n,
        invariant !has_divisor_in_range(n, 2, i),
    {
        if n % i == 0 {
            proof {
                divisor_found_means_not_prime(n, i);
            }
            return false;
        }
        i = i + 1;
    }
    
    proof {
        assert(!has_divisor_in_range(n, 2, n));
        assert(forall|k: int| 2 <= k < n ==> {
            no_divisor_means_prime(n, k);
            n % k != 0
        });
    }
    
    true
}
// </vc-code>

fn main() {
}

}