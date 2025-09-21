// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn power(a: int, n: int) -> int
    recommends 0 <= n
    decreases n when 0 <= n
{
    if n <= 0 { 1 } else { a * power(a, n - 1) }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn A8Q1(y0: u8, x: i8) -> (z: i8)
    requires y0 as int >= 0
    ensures z as int == power(x as int, y0 as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}