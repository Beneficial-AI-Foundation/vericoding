// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers are needed for this problem. */
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
/* code modified by LLM (iteration 5): Explicitly cast intermediate calculations to `i64` to prevent `i32` overflow before final division, then cast back to `i32`. */
{
    // All arithmetic operations are performed using `i64` to prevent overflow, then cast back to `i32`.
    let oldlen: i64 = (old[1] as i64) - (old[0] as i64);
    let newlen: i64 = (new[1] as i64) - (new[0] as i64);

    let scale: i32 = (newlen / oldlen) as i32;

    let num_offset_term1: i64 = (old[1] as i64) * (new[0] as i64);
    let num_offset_term2: i64 = (old[0] as i64) * (new[1] as i64);
    let num_offset: i64 = num_offset_term1 - num_offset_term2;

    let offset: i32 = (num_offset / oldlen) as i32;

    (offset, scale)
}
// </vc-code>

}
fn main() {}