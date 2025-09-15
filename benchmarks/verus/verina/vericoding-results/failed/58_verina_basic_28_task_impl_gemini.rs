// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 4): fixed mismatched types by casting integer literals to nat */
    let mut i = 2 as nat;
    while i < n
        invariant
            n >= 2,
            2 <= i <= n,
            forall|k: nat| 2 <= k < i ==> #[trigger] (n % k) != 0,
        decreases n - i
    {
        if n % i == 0 as nat {
            return false;
        }
        i = i + (1 as nat);
    }
    true
}
// </vc-code>

}
fn main() {}