// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn mid(p: i8, q: i8) -> (m: i8)

    requires 
        p as int <= q as int,
    ensures 
        p as int <= m as int <= q as int,
        (m as int) - (p as int) <= (q as int) - (m as int),
        0 <= ((q as int) - (m as int)) - ((m as int) - (p as int)) <= 1,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}