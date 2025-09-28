use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_non_prime(n: int) -> (result: bool)
    requires n >= 2
    ensures result <==> (exists|k: int| 2 <= k < n && #[trigger] (n % k) == 0)
// </vc-spec>
// <vc-code>
{
    if n == 2_int { // 2 is prime, so return false (not non-prime)
        return false;
    }
    let mut k: int = 2_int;
    while k * k <= n
        invariant
            n >= 2,
            2 <= k,
            forall|other_k: int| 2_int <= other_k && other_k < k ==> (n % other_k) != 0,
    {
        if n % k == 0_int {
            return true;
        }
        k = k + 1_int;
    }
    false
}
// </vc-code>

fn main() {}

}