// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix variable name and remove ghost */
#[verifier::spec]
fn spec_compute_scale(old0: i8, old1: i8, new0: i8, new1: i8) -> int {
    let oldlen = old1 as int - old0 as int;
    let newlen = new1 as int - new0 as int;
    newlen / oldlen
}
#[verifier::spec]
fn spec_compute_offset(old0: i8, old1: i8, new0: i8, new1: i8) -> int {
    let oldlen = old1 as int - old0 as int;
    (old1 as int * new0 as int - old0 as int * new1 as int) / oldlen
}
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
    /* code modified by LLM (iteration 5): Fix compilation error and casting */
    let old0 = old[0] as i64;
    let old1 = old[1] as i64;
    let new0 = new[0] as i64;
    let new1 = new[1] as i64;
    let oldlen = old1 - old0;
    let scale = ((new1 - new0) / oldlen) as i8;
    let offset = ((old1 * new0 - old0 * new1) / oldlen) as i8;
    (offset, scale)
}
// </vc-code>

}
fn main() {}