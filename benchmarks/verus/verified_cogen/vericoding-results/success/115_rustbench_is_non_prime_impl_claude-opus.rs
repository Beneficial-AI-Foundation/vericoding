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
{
    /* code modified by LLM (iteration 3): Added #[trigger] annotation to quantifier to fix trigger inference */
    let mut i: u32 = 2;
    while i < n
        invariant
            2 <= i <= n,
            forall|k: int| 2 <= k < i ==> #[trigger] (n as int % k) != 0,
        decreases n - i,
    {
        if n % i == 0 {
            assert(2 <= i < n);
            assert(n as int % i as int == 0);
            return true;
        }
        i = i + 1;
    }
    assert(forall|k: int| 2 <= k < n ==> #[trigger] (n as int % k) != 0);
    false
}
// </vc-code>

}
fn main() {}