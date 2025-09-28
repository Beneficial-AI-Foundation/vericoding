// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers are needed for this implementation. */
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
    /* code modified by LLM (iteration 5): implement with ghost code as parameter is nat */
    let mut i: nat = 2;
    while i < n
        invariant
            2 <= i <= n,
            forall|k: nat| 2 <= k < i ==> n % k != 0,
        decreases n - i
    {
        if n % i == 0 {
            // We have a witness `i` such that `2 <= i < n` and `n % i == 0`.
            // This is sufficient to prove the `exists` in the `!result` post-condition.
            assert(2 <= i < n && n % i == 0);
            return false;
        }
        i = i + 1;
    }
    // If the loop terminates, `i == n`.
    // The invariant `forall|k: nat| 2 <= k < i ==> n % k != 0`
    // becomes `forall|k: nat| 2 <= k < n ==> n % k != 0`,
    // which proves the postcondition for returning `true`.
    true
}
// </vc-code>

}
fn main() {}