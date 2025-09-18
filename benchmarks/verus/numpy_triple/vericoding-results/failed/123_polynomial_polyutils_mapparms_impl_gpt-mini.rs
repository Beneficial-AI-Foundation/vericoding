// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): use int-returning spec helpers to match spec arithmetic */
spec fn old_len(a: [i32; 2]) -> int { a[1] - a[0] }
spec fn new_len(a: [i32; 2]) -> int { a[1] - a[0] }
spec fn compute_scale(old: [i32; 2], new: [i32; 2]) -> int { (new[1] - new[0]) / (old[1] - old[0]) }
spec fn compute_offset(old: [i32; 2], new: [i32; 2]) -> int { (old[1] * new[0] - old[0] * new[1]) / (old[1] - old[0]) }
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
    /* code modified by LLM (iteration 5): compute scale and offset using i32 arithmetic */
    let oldlen: i32 = old[1] - old[0];
    let newlen: i32 = new[1] - new[0];
    let scale: i32 = newlen / oldlen;
    let offset: i32 = (old[1] * new[0] - old[0] * new[1]) / oldlen;
    (offset, scale)
}
// </vc-code>

}
fn main() {}