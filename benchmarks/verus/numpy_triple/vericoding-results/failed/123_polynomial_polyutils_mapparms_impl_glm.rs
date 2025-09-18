// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added type annotation to closure parameter in ensures */
fn mapparms_impl(old0: i32, old1: i32, new0: i32, new1: i32) -> (i32, i32)
    requires old0 != old1,
    ensures(|result: (i32, i32)| {
        let (offset, scale) = result;
        let oldlen = old1 - old0;
        let newlen = new1 - new0;
        offset + scale * old0 == new0 &&
        offset + scale * old1 == new1 &&
        scale == newlen / oldlen &&
        offset == (old1 * new0 - old0 * new1) / oldlen
    })
{
    let oldlen = old1 - old0;
    let newlen = new1 - new0;
    let scale = newlen / oldlen;
    let offset = (old1 * new0 - old0 * new1) / oldlen;
    (offset, scale)
}
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
    /* code modified by LLM (iteration 5): updated comment to reflect current iteration */
    let (offset, scale) = mapparms_impl(old[0], old[1], new[0], new[1]);
    (offset, scale)
}
// </vc-code>

}
fn main() {}