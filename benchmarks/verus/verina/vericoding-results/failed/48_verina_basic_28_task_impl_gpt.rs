// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): kept spec helpers for divisibility and primality; no changes to executable code */
proof fn helper_trivial() { }

spec fn has_divisor_in_range(n: nat) -> bool {
    exists|k: nat| 2 <= k < n && #[trigger] (n % k) == 0
}

spec fn is_prime_spec(n: nat) -> bool
    recommends n >= 2
{
    !has_divisor_in_range(n)
}
// </vc-helpers>

// <vc-spec>
fn is_prime(n: nat) -> (result: bool)
    requires n >= 2,
    ensures
        result ==> forall|k: nat| 2 <= k < n ==> #[trigger] (n % k) != 0,
        !result ==> exists|k: nat| 2 <= k < n && #[trigger] (n % k) == 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use nat-typed literals via casts and maintain loop invariants */
    let mut k: nat = 2 as nat;
    while k < n
        invariant
            n >= 2,
            2 <= k && k <= n,
            forall|j: nat| 2 <= j < k ==> #[trigger] (n % j) != 0
        decreases n - k
    {
        if (n % k) == 0 as nat {
            proof {
                assert(2 <= k && k < n);
                assert(exists|kk: nat| kk == k && 2 <= kk < n && #[trigger] (n % kk) == 0);
            }
            return false;
        }
        k = k + 1 as nat;
    }
    proof {
        assert(k == n);
        assert(forall|j: nat| 2 <= j < n ==> #[trigger] (n % j) != 0);
    }
    true
}
// </vc-code>

}
fn main() {}