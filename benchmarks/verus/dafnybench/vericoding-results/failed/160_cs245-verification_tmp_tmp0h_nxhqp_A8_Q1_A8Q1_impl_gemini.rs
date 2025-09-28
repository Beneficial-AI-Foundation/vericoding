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
fn A8Q1(y0: int, x: int) -> (z: int)
    requires y0 >= 0
    ensures z == power(x, y0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): add explicit type annotations for local variables */
    let mut z: int = 1;
    let mut y: int = y0;

    while y > 0
        invariant
            y >= 0,
            y <= y0,
            z == power(x, y0 - y),
        decreases y
    {
        z = z * x;
        y = y - 1;
    }
    z
}
// </vc-code>

}
fn main() {}