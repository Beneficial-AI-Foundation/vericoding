// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn has_divisor(n: nat, k: nat) -> bool
    requires
        k >= 2,
        n >= 2,
    decreases n - k,
{
    if k >= n {
        false
    } else if (n % k == 0) {
        true
    } else {
        has_divisor(n, k + 1)
    }
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
/* code modified by LLM (iteration 4): use nat literal 2nat for divisor check */
{
    !has_divisor(n, 2nat)
}
// </vc-code>

}
fn main() {}