use vstd::prelude::*;

verus! {

spec fn is_prime_pred(n: u32) -> (ret: bool) {
    forall|k: int| 2 <= k < n ==> #[trigger] (n as int % k) != 0
}

// <vc-helpers>
fn is_prime_check(p: u32) -> (ret: bool)
    requires
        2u32 <= p,
    ensures
        ret ==> is_prime_pred(p)
{
    let mut k: int = 2;
    while k < (p as int)
        invariant 2 <= k;
        invariant k <= (p as int);
        invariant forall|i: int| 2 <= i && i < k ==> #[trigger] (p as int % i) != 0;
    {
        if (p as int % k) == 0 {
            return false;
        }
        k += 1;
    }
    proof {
        assert(k == p as int);
        assert(forall|i: int| 2 <= i && i < (p as int) ==> #[trigger] (p as int % i) != 0);
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
    let mut p: u32 = 2u32;
    let mut last: u32 = 1u32;
    while p <= n
        invariant 2u32 <= p;
        invariant p <= n + 1u32;
        invariant 1u32 <= last;
        invariant last <= n;
        invariant last == 1u32 || (last > 1u32 && is_prime_pred(last));
    {
        if n % p == 0u32 {
            if is_prime_check(p) {
                last = p;
            }
        }
        p += 1u32;
    }
    last
    // impl-end
}
// </vc-code>

fn main() {}
}