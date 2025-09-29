// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_ln10_bounds()
    ensures
        0 <= 2,
        1 <= 2,
        2 <= 2,
        2 <= 3,
{
}

// </vc-helpers>

// <vc-spec>
fn npy_loge10() -> (result: i8)
    ensures
        /* Mathematical property: ln(10) is positive (since 10 > 1) */
        result as int >= 0,
        /* Mathematical property: ln(10) > ln(e) = 1 (since 10 > e) */  
        result as int >= 1,
        /* Mathematical property: ln(10) is between 2 and 3 */
        2 <= result as int && result as int <= 3,
// </vc-spec>
// <vc-code>
{
    2i8
}
// </vc-code>


}
fn main() {}