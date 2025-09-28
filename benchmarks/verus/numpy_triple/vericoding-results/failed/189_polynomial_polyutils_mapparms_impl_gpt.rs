// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): placeholder lemma to keep arithmetic reasoning in ghost context */
proof fn trivial_helper(o0: int, o1: int, n0: int, n1: int)
    requires
        o0 != o1,
    ensures
        true,
{
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
    /* code modified by LLM (iteration 2): avoid using 'int' in exec code; compute with i32 temporaries and cast to i8 */
    let o0_i32: i32 = old[0] as i32;
    let o1_i32: i32 = old[1] as i32;
    let n0_i32: i32 = new[0] as i32;
    let n1_i32: i32 = new[1] as i32;

    let ol: i32 = o1_i32 - o0_i32;
    let nl: i32 = n1_i32 - n0_i32;

    let scale_i32: i32 = nl / ol;
    let offset_i32: i32 = (o1_i32 * n0_i32 - o0_i32 * n1_i32) / ol;

    let scale: i8 = scale_i32 as i8;
    let offset: i8 = offset_i32 as i8;
    (offset, scale)
}
// </vc-code>

}
fn main() {}