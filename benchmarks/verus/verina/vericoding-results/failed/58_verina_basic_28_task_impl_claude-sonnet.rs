// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): empty helpers section - no additional helpers needed */
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
    /* code modified by LLM (iteration 5): fix nat literals by using proper nat conversion syntax */
    let mut i: nat = 2;
    
    while i < n
        invariant
            2 <= i <= n,
            forall|k: nat| 2 <= k < i ==> n % k != 0
    {
        if n % i == 0 {
            return false;
        }
        i = i + 1;
    }
    
    true
}
// </vc-code>

}
fn main() {}