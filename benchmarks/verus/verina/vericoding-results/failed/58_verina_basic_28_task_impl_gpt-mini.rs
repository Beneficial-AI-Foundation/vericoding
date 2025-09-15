// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): defines divisor predicate */
spec fn is_divisor(n: nat, k: nat) -> bool { 2 <= k && k < n && n % k == 0 }
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
    /* code modified by LLM (iteration 3): iterate over potential divisors using nat typed counters */
    let mut i: nat = 2;
    let mut found: bool = false;
    let mut witness: nat = 0;
    while i < n
        invariant 2 <= i <= n && (!found ==> forall|k: nat| 2 <= k < i ==> n % k != 0) && (found ==> 2 <= witness && witness < n && n % witness == 0),
        decreases n - i
    {
        if n % i == 0 {
            witness = i;
            found = true;
            break;
        }
        i = i + 1;
    }
    if found {
        proof {
            assert(2 <= witness && witness < n && n % witness == 0);
        }
        false
    } else {
        proof {
            // from loop exit: i >= n, together with invariant 2 <= i <= n gives i == n
            assert(i >= n);
            assert(i <= n);
            assert(i == n);
            assert(forall|k: nat| 2 <= k < i ==> n % k != 0);
            // since i == n, we obtain the desired property for all k with 2 <= k < n
            assert(forall|k: nat| 2 <= k < n ==> n % k != 0);
        }
        true
    }
}
// </vc-code>

}
fn main() {}