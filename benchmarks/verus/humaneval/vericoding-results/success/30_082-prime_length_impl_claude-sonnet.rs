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
/* helper modified by LLM (iteration 3): fixed postcondition logic for false case */
fn check_prime_helper(n: usize) -> (result: bool)
    requires n >= 2
    ensures result == is_prime(n as int)
{
    let mut i = 2;
    while i < n
        invariant
            2 <= i <= n,
            forall|k: int| 2 <= k < i ==> !is_divisible(n as int, k)
        decreases n - i
    {
        if n % i == 0 {
            proof {
                assert(is_divisible(n as int, i as int));
                assert(2 <= i < n);
                assert(!is_prime(n as int));
            }
            return false;
        }
        i += 1;
    }
    proof {
        assert(forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k));
        assert(is_prime(n as int));
    }
    true
}
// </vc-helpers>

// <vc-spec>
fn prime_length(str: &[char]) -> (result: bool)

    ensures
        result == is_prime(str.len() as int),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): added proof block for specification matching */
{
    let len = str.len();
    if len < 2 {
        proof {
            assert(!is_prime(len as int));
        }
        false
    } else {
        check_prime_helper(len)
    }
}
// </vc-code>

}
fn main() {}