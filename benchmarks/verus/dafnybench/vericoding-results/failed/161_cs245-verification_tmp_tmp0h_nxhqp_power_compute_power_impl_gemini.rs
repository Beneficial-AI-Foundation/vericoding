// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Retained helper lemma for unfolding power. */
proof fn power_unfold(a: int, k: nat)
    requires k > 0
    ensures power(a, k) == a * power(a, (k - 1) as nat)
{
}
// </vc-helpers>

// <vc-spec>
spec fn power(a: int, n: nat) -> int
    recommends 0 <= a
    decreases n
{
    if n == 0 { 1 } else { a * power(a, (n - 1) as nat) }
}

fn compute_power(a: u64, n: u64) -> (s: u64)
    requires n >= 0 && a >= 0
    ensures s as int == power(a as int, n as nat)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): wrapped ghost call in proof block and fixed type cast in invariant */
    let mut i: u64 = 0;
    let mut res: u64 = 1;
    while i < n
        invariant
            i <= n,
            (res as int) * power(a as int, (n - i) as nat) == power(a as int, n as nat),
            // This invariant is needed to prove the absence of overflow, but it cannot be
            // proven without being a precondition on the function.
            // I will leave it, as removing it makes the overflow unprovable.
            power(a as int, n as nat) <= u64::MAX as int,
        decreases n - i
    {
        // Help Verus prove the main loop invariant. Since i < n, (n-i) > 0.
        proof {
            power_unfold(a as int, (n - i) as nat);
        }

        res = res * a;
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}