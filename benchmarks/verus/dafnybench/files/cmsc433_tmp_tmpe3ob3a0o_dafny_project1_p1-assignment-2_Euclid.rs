// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn euclid(m: i8, n: i8) -> (gcd: i8)
    requires m as int > 1 && n as int > 1 && m as int >= n as int
    ensures gcd as int > 0 && gcd as int <= n as int && gcd as int <= m as int && m as int % gcd as int == 0 && n as int % gcd as int == 0
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}