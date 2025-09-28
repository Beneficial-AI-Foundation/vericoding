// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added trigger annotations to fix quantifier inference */
spec fn divides(a: int, b: int) -> bool { b != 0 && a % b == 0 }

proof fn divisor_exists_lemma(n: u32, k: u32)
    requires
        n >= 2,
        k >= 2,
        k < n,
        (n as int) % (k as int) == 0,
    ensures
        exists|d: int| 2 <= d < n && #[trigger] (n as int % d) == 0,
{
    assert((n as int) % (k as int) == 0);
}
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
/* code modified by LLM (iteration 2): added trigger annotation to fix quantifier inference error */
{
    let mut k: u32 = 2;
    while k < n
        invariant
            k >= 2,
            k <= n,
            forall|j: int| 2 <= j < k ==> #[trigger] (n as int % j) != 0,
        decreases n - k
    {
        if n % k == 0 {
            proof {
                divisor_exists_lemma(n, k);
            }
            return true;
        }
        k = k + 1;
    }
    return false;
}
// </vc-code>

}
fn main() {}