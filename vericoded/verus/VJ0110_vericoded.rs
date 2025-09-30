// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_divisible(n: int, divisor: int) -> (result: bool) {
    (n % divisor) == 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn prime_num(n: u64) -> (result: bool)

    requires
        n >= 2,

    ensures
        result == (forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added proof block to justify false return path */
    let mut i: u64 = 2;
    while i < n
        invariant
            2 <= i <= n,
            forall|k: int| 2 <= k < i as int ==> !is_divisible(n as int, k),
        decreases n - i
    {
        if n % i == 0 {
            proof {
                // Postcondition for returning false is:
                // exists|k: int| 2 <= k < n && is_divisible(n, k)
                // We prove this by showing 'i' is the witness.
                assert(is_divisible(n as int, i as int)); // from `n % i == 0`
                assert(2 <= (i as int) && (i as int) < (n as int)); // from loop invariant and condition
            }
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}