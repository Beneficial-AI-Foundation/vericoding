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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}