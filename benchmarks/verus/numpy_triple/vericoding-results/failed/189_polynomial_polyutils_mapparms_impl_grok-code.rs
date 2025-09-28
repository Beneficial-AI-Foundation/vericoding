// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn mapparms(old: [i8; 2], new: [i8; 2]) -> (result: (i8, i8))
    requires old[0] != old[1],
    ensures ({
        let (offset, scale) = result;
        let oldlen = old[1] as int - old[0] as int;
        let newlen = new[1] as int - new[0] as int;
        offset as int + scale as int * old[0] as int == new[0] as int &&
        offset as int + scale as int * old[1] as int == new[1] as int &&
        scale as int == newlen / oldlen &&
        offset as int == (old[1] as int * new[0] as int - old[0] as int * new[1] as int) / oldlen
    })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Using int for intermediate calculations and truncate on casts to avoid overflow warnings and truncation recommendations */
    let old0 = old[0] as int;
    let old1 = old[1] as int;
    let new0 = new[0] as int;
    let new1 = new[1] as int;
    let oldlen = old1 - old0;
    let newlen = new1 - new0;
    let scale = newlen / oldlen;
    let offset = (old1 * new0 - old0 * new1) / oldlen;
    (#[verifier::truncate] offset as i8, #[verifier::truncate] scale as i8)
}
// </vc-code>

}
fn main() {}