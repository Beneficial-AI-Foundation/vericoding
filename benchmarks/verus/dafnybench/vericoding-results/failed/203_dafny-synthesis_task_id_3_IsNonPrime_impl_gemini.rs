// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_non_prime(n: int) -> (result: bool)
    requires n >= 2
    ensures result <==> (exists|k: int| 2 <= k < n && #[trigger] (n % k) == 0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Used `u64` for executable variables to fix compilation errors. */
    let mut i: u64 = 2;
    while i < n
        invariant
            n >= 2,
            2 <= i,
            i <= n,
            forall|k: int| 2 <= k < i ==> n % k != 0,
        decreases n - i
    {
        if n % i == 0 {
            return true;
        }
        i = i + 1;
    }
    return false;
}
// </vc-code>

}
fn main() {}