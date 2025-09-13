// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, a: int, b: int, p: int, q: int) -> bool {
    n > 0 && a > 0 && b > 0 && p > 0 && q > 0
}

spec fn gcd(a: int, b: int) -> int
    decreases b
{
    if b == 0 { a } else { gcd(b, a % b) }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, a: int, b: int, p: int, q: int) -> (result: int)
    requires valid_input(n, a, b, p, q)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}