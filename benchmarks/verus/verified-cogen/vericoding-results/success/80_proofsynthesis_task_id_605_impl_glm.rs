// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_divisible(n: int, divisor: int) -> (result: bool) {
    (n % divisor) == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added executable divisibility check */
fn checked_divisible(n: u64, divisor: u64) -> (result: bool)
    requires
        divisor != 0,
    ensures
        result == (is_divisible(n as int, divisor as int))
{
    n % divisor == 0
}
// </vc-helpers>

// <vc-spec>
fn prime_num(n: u64) -> (result: bool)

    requires
        n >= 2,

    ensures
        result == (forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k)),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): added decreases clause to loop */
{
    let mut i: u64 = 2;
    while i < n
        invariant
            2 <= i <= n,
            forall|k: int| 2 <= k < (i as int) ==> !is_divisible(n as int, k)
        decreases n - i
    {
        if checked_divisible(n, i) {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}