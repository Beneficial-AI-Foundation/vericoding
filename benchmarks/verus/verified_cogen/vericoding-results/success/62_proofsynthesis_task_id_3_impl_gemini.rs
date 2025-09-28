// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_divisible(n: int, divisor: int) -> bool {
    (n % divisor) == 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_non_prime(n: u64) -> (result: bool)

    requires
        n >= 2,

    ensures
        result == (exists|k: int| 2 <= k < n && is_divisible(n as int, k)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to prove loop termination */
    let mut k: u64 = 2;
    while k < n
        invariant
            n >= 2,
            2 <= k <= n,
            forall|j: int| 2 <= j < (k as int) ==> !is_divisible(n as int, j),
        decreases n - k
    {
        if n % k == 0 {
            assert(is_divisible(n as int, k as int));
            return true;
        }
        k = k + 1;
    }
    return false;
}
// </vc-code>

}
fn main() {}