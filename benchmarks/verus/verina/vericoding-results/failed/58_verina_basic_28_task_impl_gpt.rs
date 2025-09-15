// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): predicate to state divisibility in an allowed range */
spec fn is_divisor(n: nat, k: nat) -> bool { 2 <= k && k < n && n % k == 0 }
/* helper modified by LLM (iteration 2): trivial reflexivity lemma used for simple sanity checks */
proof fn lemma_trivial_refl(x: int) ensures x == x { }
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
    /* code modified by LLM (iteration 2): implemented divisor search with proper loop invariants */
    let mut i: nat = 2;
    let mut found: bool = false;
    let mut w: nat = 2;

    while i < n
        invariant 2 <= i && i <= n
        invariant found ==> (2 <= w && w < i && n % w == 0)
        invariant !found ==> forall|k: nat| 2 <= k && k < i ==> n % k != 0
        decreases n - i
    {
        if n % i == 0 {
            found = true;
            w = i;
        }
        i = i + 1;
    }

    assert(i == n);

    if found {
        assert(2 <= w && w < i && n % w == 0);
        assert(w < n);
        false
    } else {
        assert(forall|k: nat| 2 <= k && k < n ==> n % k != 0);
        true
    }
}
// </vc-code>

}
fn main() {}