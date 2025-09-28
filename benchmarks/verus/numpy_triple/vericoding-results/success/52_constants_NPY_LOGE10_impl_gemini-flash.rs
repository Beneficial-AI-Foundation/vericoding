// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    // npy_loge10 is likely 2 or 3 based on standard IEEE 754 floating point approximations
    // of log_e(10). The Verus `as` operator handles two's complement behavior for signed integers
    // where an out-of-range value is truncated and the bit pattern stored. Since 2 and 3
    // fit into i8 without truncation this is safe for positive values.
    let result: i8 = 2i8;
    result
}
// </vc-code>


}
fn main() {}