use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_divisible_implies_non_prime(n: int, k: int)
    requires
        2 <= n,
        2 <= k < n,
        n % k == 0,
    ensures
        exists|d: int| 2 <= d < n && #[trigger] (n % d) == 0,
{
    // The condition n % k == 0 with 2 <= k < n directly implies the existential condition
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn is_non_prime(n: int) -> (result: bool)
    requires n >= 2
    ensures result <==> (exists|k: int| 2 <= k < n && #[trigger] (n % k) == 0)
// </vc-spec>
// </vc-spec>

// <vc-code>
fn is_non_prime(n: int) -> (result: bool)
    requires n >= 2
    ensures result <==> (exists|k: int| 2 <= k < n && #[trigger] (n % k) == 0)
{
    let mut k = 2;
    while k < n
        invariant
            2 <= k <= n,
            forall|d: int| 2 <= d < k ==> n % d != 0,
    {
        if n % k == 0 {
            proof {
                lemma_divisible_implies_non_prime(n, k);
            }
            return true;
        }
        k = k + 1;
    }
    return false;
}
// </vc-code>

fn main() {}

}