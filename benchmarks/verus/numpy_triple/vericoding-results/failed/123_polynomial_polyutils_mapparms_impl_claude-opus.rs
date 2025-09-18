// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn mapparms(old: [i32; 2], new: [i32; 2]) -> (result: (i32, i32))
    requires old[0] != old[1],
    ensures ({
        let (offset, scale) = result;
        let oldlen = old[1] - old[0];
        let newlen = new[1] - new[0];
        offset + scale * old[0] == new[0] &&
        offset + scale * old[1] == new[1] &&
        scale == newlen / oldlen &&
        offset == (old[1] * new[0] - old[0] * new[1]) / oldlen
    })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Add bounds checks for arithmetic operations */
    let oldlen = (old[1] as i64) - (old[0] as i64);
    let newlen = (new[1] as i64) - (new[0] as i64);
    let scale = (newlen / oldlen) as i32;
    
    let old1_i64 = old[1] as i64;
    let new0_i64 = new[0] as i64;
    let old0_i64 = old[0] as i64;
    let new1_i64 = new[1] as i64;
    
    assert(old1_i64 * new0_i64 >= i64::MIN && old1_i64 * new0_i64 <= i64::MAX);
    assert(old0_i64 * new1_i64 >= i64::MIN && old0_i64 * new1_i64 <= i64::MAX);
    let prod1 = old1_i64 * new0_i64;
    let prod2 = old0_i64 * new1_i64;
    assert(prod1 - prod2 >= i64::MIN && prod1 - prod2 <= i64::MAX);
    
    let offset = ((prod1 - prod2) / oldlen) as i32;
    (offset, scale)
}
// </vc-code>

}
fn main() {}