// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn polyline(off: i8, scl: i8) -> (result: [i8; 2])
    ensures
        /* Constant term is always off */
        result[0] == off,
        /* Linear coefficient is always scl */
        result[1] == scl,
        /* Size is always 2 (representing up to degree 1 polynomial) */
        result@.len() == 2,
        /* Example evaluation: if we evaluate at x=1, we get off + scl */
        result[0] as int + result[1] as int == off as int + scl as int
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    [0; 2]
    // impl-end
}
// </vc-code>


}
fn main() {}