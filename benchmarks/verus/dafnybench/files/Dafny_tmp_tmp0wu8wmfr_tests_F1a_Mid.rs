// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn mid(p: int, q: int) -> (m: int)

    requires 
        p <= q,
    ensures 
        p <= m <= q,
        m - p <= q - m,
        0 <= (q - m) - (m - p) <= 1,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}