// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_divisible(n: int, divisor: int) -> (ret:bool) {
    (n % divisor) == 0
}

spec fn is_prime(n: int) -> (ret:bool) {
    if n < 2 {
        false
    } else {
        (forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed postcondition verification by adding assert to prove no divisors exist */
fn is_prime_exec(n: usize) -> (result: bool)
    ensures
        result == is_prime(n as int),
{
    if n < 2 {
        return false;
    }
    let mut k: usize = 2;
    while k < n
        invariant
            2 <= k <= n,
            forall|j: int| 2 <= j < k ==> !is_divisible(n as int, j),
        decreases n - k
    {
        if n % k == 0 {
            assert(is_divisible(n as int, k as int));
            assert(!is_prime(n as int));
            return false;
        }
        k = k + 1;
    }
    assert(forall|j: int| 2 <= j < n ==> !is_divisible(n as int, j));
    true
}
// </vc-helpers>

// <vc-spec>
fn prime_length(str: &[char]) -> (result: bool)

    ensures
        result == is_prime(str.len() as int),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): call helper function to check primality */
{
    let n = str.len();
    is_prime_exec(n)
}
// </vc-code>

}
fn main() {}