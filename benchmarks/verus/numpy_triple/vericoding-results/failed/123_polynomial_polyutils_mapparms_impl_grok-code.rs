// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): no helpers added */
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
/* code modified by LLM (iteration 3): used i128 for intermediate calculations to avoid overflow warnings in multiplications and divisions */
    let old0: i128 = old[0] as i128;
    let old1: i128 = old[1] as i128;
    let new0: i128 = new[0] as i128;
    let new1: i128 = new[1] as i128;
    let oldlen: i128 = old1 - old0;
    let newlen: i128 = new1 - new0;
    let scale: i32 = #[verifier::truncate] ((newlen / oldlen) as i32);
    let offset: i32 = #[verifier::truncate] ((((old1 * new0) - (old0 * new1)) / oldlen) as i32);
    (offset, scale)
}
// </vc-code>

}
fn main() {}