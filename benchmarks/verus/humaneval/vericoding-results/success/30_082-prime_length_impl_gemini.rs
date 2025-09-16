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
proof fn lemma_divisible_implies_not_prime(n: int, k: int)
    requires
        2 <= k < n,
        is_divisible(n, k),
    ensures
        !is_prime(n),
{
}

/* helper added by LLM (iteration 2): executable version of is_divisible */
fn is_divisible_exec(n: usize, divisor: usize) -> (ret: bool)
    requires divisor > 0,
    ensures ret == is_divisible(n as int, divisor as int),
{
    (n % divisor) == 0
}

/* helper modified by LLM (iteration 3): wrap lemma call in proof block to fix cast error */
fn is_prime_exec(n: usize) -> (b: bool)
    ensures b == is_prime(n as int),
{
    if n < 2 {
        return false;
    }
    let mut i: usize = 2;
    while i < n
        invariant
            n >= 2,
            2 <= i <= n,
            forall|k: int| 2 <= k < (i as int) ==> !is_divisible(n as int, k),
        decreases n - i
    {
        if is_divisible_exec(n, i) {
            proof {
                lemma_divisible_implies_not_prime(n as int, i as int);
            }
            return false;
        }
        i = i + 1;
    }
    return true;
}
// </vc-helpers>

// <vc-spec>
fn prime_length(str: &[char]) -> (result: bool)

    ensures
        result == is_prime(str.len() as int),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): call helper function to check primality of length */
{
    let len = str.len();
    is_prime_exec(len)
}
// </vc-code>

}
fn main() {}