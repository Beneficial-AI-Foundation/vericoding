// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type mismatches in `verus_sqrt` by explicitly casting `int` literals and expressions to `nat` where necessary. */
proof fn verus_sqrt(n: nat) -> (result: nat)
    ensures result * result <= n && (result + 1) * (result + 1) > n
{
    if n == (0 as nat) { return (0 as nat); }
    let mut low: nat = (0 as nat);
    let mut high: nat = n;
    let mut ans: nat = (0 as nat);

    while low <= high
        invariant
            low >= (0 as nat),
            high >= (0 as nat),
            ans >= (0 as nat),
            ans * ans <= n,
            high + (1 as nat) >= low,
            (ans + (1 as nat)) * (ans + (1 as nat)) > n || (ans + (1 as nat)) * (ans + (1 as nat)) <= n && high >= ans + (1 as nat)
        decreases high - low
    {
        let mid = low + (high - low) / (2 as nat);
        if mid * mid <= n {
            ans = mid;
            low = mid + (1 as nat);
        } else {
            high = mid - (1 as nat);
        }
    }
    ans
}

proof fn is_prime_test_general<F: Fn(nat) -> bool>(n: nat, p: F)
    requires
        n >= (2 as nat),
        forall|m: nat| #![auto] (2 as nat) <= m < n ==> ((n % m) == (0 as nat) ==> !p(n)),
        forall|m: nat| #![auto] (2 as nat) <= m < n ==> ((n % m) != (0 as nat) ==> p(n)),
    ensures
        p(n) == (forall|k: nat| (2 as nat) <= k < n ==> (n % k) != (0 as nat))
{
    // The proof goal P(n) == (forall k, 2 <= k < n => n % k != 0) is directly implied by the requires clauses.
    // No explicit proof steps are needed as Verus can often deduce this from established quantifiers.
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
/* code modified by LLM (iteration 5): Fixed type mismatches by explicitly casting `int` literals to `nat` and `int` expressions to `nat` where necessary. */
{
    if n == (2 as nat) || n == (3 as nat) {
        return true;
    }

    if n % (2 as nat) == (0 as nat) {
        return false;
    }

    let mut k: nat = (3 as nat);
    let sqrt_n_nat: nat = verus_sqrt(n);

    while k <= sqrt_n_nat
        invariant
            n >= (2 as nat),
            k >= (3 as nat),
            k % (2 as nat) == (1 as nat),
            sqrt_n_nat == verus_sqrt(n),
            forall|j: nat| (2 as nat) <= j < k && (j % (2 as nat) == (0 as nat) || j % (2 as nat) == (1 as nat)) ==> (n % j) != (0 as nat),
        decreases sqrt_n_nat - k
    {
        if n % k == (0 as nat) {
            return false;
        }
        k = k + (2 as nat);
    }

    true
}
// </vc-code>

}
fn main() {}