// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn is_non_prime(n: u32) -> (result: bool)
    requires
        n >= 2,
    ensures
        result == exists|k: int| 2 <= k < n && #[trigger] (n as int % k) == 0,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed the loop invariant trigger without moving it. Removing the trigger was not the right fix, as there was no trigger previously. Instead, `#[trigger]` was added to the `(n as int % j) != 0` within the forall statement to comply with trigger requirements. */
{
    if n < 2 {
        return false;
    }
    let mut k: u32 = 2;
    while k < n
        invariant
            k >= 2,
            k <= n,
            forall|j: int| 2 <= j < k as int ==> #[trigger] (n as int % j) != 0
        decreases n - k
    {
        if n % k == 0 {
            return true;
        }
        k = k + 1;
    }
    false
}
// </vc-code>

}
fn main() {}