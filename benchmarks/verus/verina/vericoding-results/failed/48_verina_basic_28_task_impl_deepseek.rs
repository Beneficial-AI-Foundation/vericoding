// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn is_prime_helper(n: nat, k: nat) -> (result: bool)
    requires
        n >= 2,
        k >= 2,
        k <= n,
    ensures
        result ==> forall|i: nat| 2 <= i < k ==> #[trigger] (n % i) != 0,
        !result ==> exists|i: nat| 2 <= i < k && #[trigger] (n % i) == 0,
{
    /* helper modified by LLM (iteration 5): Fixed compilation error by removing extra parameter */
    if k == 2 {
        true
    } else {
        let prev_result = is_prime_helper(n, (k - 1) as nat);
        if prev_result {
            (n % ((k - 1) as nat) != 0)
        } else {
            false
        }
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
{
    /* code modified by LLM (iteration 5): Fixed compilation error by using executable function */
    let mut k: int = 2;
    while k < n
        invariant
            2 <= k <= n,
            forall|i: nat| 2 <= i < k ==> #[trigger] (n % i) != 0,
        decreases n - k
    {
        if n % k == 0 {
            return false;
        }
        k = k + 1;
    }
    true
}
// </vc-code>

}
fn main() {}