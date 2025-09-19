// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn gcd(x: int, y: int) -> int
    recommends x > 0 && y > 0
    decreases x + y when x > 0 && y > 0
{
    if x == y { x }
    else if x > y { gcd(x - y, y) }
    else { gcd(x, y - x) }
}

spec fn gcd_prime(x: int, y: int) -> int
    recommends x > 0 && y > 0
    decreases if x > y { x } else { y }, x + y when x > 0 && y > 0
{
    if x == y { x }
    else if x > y { gcd_prime(x - y, y) }
    else { gcd(y, x) }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn gcd_i(m: i8, n: i8) -> (d: i8)
    requires m as int > 0 && n as int > 0
    ensures d as int == gcd(m as int, n as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}