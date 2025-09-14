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
    /* code modified by LLM (iteration 2): added decreases clause to fix loop verification */
    if n == 2 {
        return false;
    }
    
    let mut i: u64 = 2;
    while i < n
        invariant
            2 <= i <= n,
            forall|k: int| 2 <= k < i ==> !is_divisible(n as int, k),
        decreases n - i,
    {
        if n % i == 0 {
            assert(is_divisible(n as int, i as int));
            return true;
        }
        i = i + 1;
    }
    
    assert(forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k));
    false
}
// </vc-code>

}
fn main() {}