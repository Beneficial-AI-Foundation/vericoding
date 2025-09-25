// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn euclid(m: int, n: int) -> (gcd: int)
    requires m > 1 && n > 1 && m >= n
    ensures gcd > 0 && gcd <= n && gcd <= m && m % gcd == 0 && n % gcd == 0
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}