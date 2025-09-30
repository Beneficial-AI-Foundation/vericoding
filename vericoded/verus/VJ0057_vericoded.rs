// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_divisible(n: int, divisor: int) -> bool {
    (n % divisor) == 0
}
// </vc-preamble>

// <vc-helpers>
proof fn divisibility_check_lemma(n: u64, k: u64)
    requires
        2 <= k < n,
        n % k == 0,
    ensures
        is_divisible(n as int, k as int),
{
}

proof fn non_divisibility_lemma(n: u64, k: u64)
    requires
        2 <= k < n,
        n % k != 0,
    ensures
        !is_divisible(n as int, k as int),
{
}
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
    let mut i = 2u64;
    while i < n
        invariant
            2 <= i <= n,
            forall|k: int| 2 <= k < i ==> !is_divisible(n as int, k),
        decreases n - i
    {
        if n % i == 0 {
            proof {
                divisibility_check_lemma(n, i);
            }
            return true;
        }
        proof {
            non_divisibility_lemma(n, i);
        }
        i = i + 1;
    }
    return false;
}
// </vc-code>

}
fn main() {}