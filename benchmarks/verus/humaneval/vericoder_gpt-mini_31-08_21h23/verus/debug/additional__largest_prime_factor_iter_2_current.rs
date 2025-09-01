use vstd::prelude::*;

verus! {

spec fn is_prime_pred(n: u32) -> (ret: bool) {
    forall|k: int| 2 <= k < n ==> #[trigger] (n as int % k) != 0
}

// <vc-helpers>
fn is_prime_check(p: u32) -> (ret: bool)
    requires
        2 <= p,
    ensures
        ret ==> is_prime_pred(p)
{
    let mut k: u32 = 2;
    while k < p {
        invariant 2 <= k;
        invariant k <= p;
        invariant forall|i: int| 2 <= i && i < k ==> #[trigger] (p as int % i) != 0;
        if p % k == 0 {
            return false;
        }
        k += 1;
    }
    proof {
        assert(k == p);
        assert(forall|i: int| 2 <= i && i < p ==> #[trigger] (p as int % i) != 0);
    }
    true
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn largest_prime_factor(n: u32) -> (result: u32)
    requires
        2 <= n <= u32::MAX - 1,
    ensures
        1 <= result <= n,
        result == 1 || (result > 1 && is_prime_pred(result))
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut p: u32 = 2;
    let mut last: u32 = 1;
    while p <= n {
        invariant 2 <= p;
        invariant p <= n + 1;
        invariant 1 <= last;
        invariant last <= n;
        invariant last == 1 || (last > 1 && is_prime_pred(last));
        if n % p == 0 {
            if is_prime_check(p) {
                last = p;
            }
        }
        p += 1;
    }
    last
    // impl-end
}
// </vc-code>

fn main() {}
}