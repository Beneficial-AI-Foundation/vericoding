// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn quotient(x: u8, y: u8) -> (result: (i8, i8))
    requires y != 0
    ensures ({
        let (r, q) = result;
        (q as int) * (y as int) + (r as int) == (x as int) && 0 <= (r as int) < (y as int) && 0 <= (q as int)
    })
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}