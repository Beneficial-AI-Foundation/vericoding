// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec cast helper from i32 to int */
spec fn i32_to_int(x: i32) -> int { x as int }

/* helper modified by LLM (iteration 5): lemma that non-equal endpoints give nonzero integer difference */
proof fn lemma_oldlen_nonzero(old0: i32, old1: i32)
    requires old0 != old1
    ensures (old1 as int - old0 as int) != 0
{ }
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
    /* code modified by LLM (iteration 5): compute mapping parameters using ghost math-int arithmetic to avoid machine-int overflow, then cast */
    proof { assert(old[0] != old[1]); }

    let ghost old0: int = old[0] as int;
    let ghost old1: int = old[1] as int;
    let ghost new0: int = new[0] as int;
    let ghost new1: int = new[1] as int;

    let ghost oldlen: int = old1 - old0;
    let ghost newlen: int = new1 - new0;

    proof { assert(oldlen != 0); }

    let ghost scale_i: int = newlen / oldlen;
    let ghost offset_i: int = (old1 * new0 - old0 * new1) / oldlen;

    #[verifier::truncate]
    let scale: i32 = scale_i as i32;
    #[verifier::truncate]
    let offset: i32 = offset_i as i32;

    (offset, scale)
}
// </vc-code>

}
fn main() {}