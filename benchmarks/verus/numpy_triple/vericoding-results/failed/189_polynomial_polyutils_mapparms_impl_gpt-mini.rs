// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): convert i8 to int */
spec fn i8_to_int(x: i8) -> int {
    x as int
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
    /* code modified by LLM (iteration 5): compute scale and offset using int arithmetic to avoid i8 underflow */
    let old0: i8 = old[0];
    let old1: i8 = old[1];
    let new0: i8 = new[0];
    let new1: i8 = new[1];
    let oldlen: int = i8_to_int(old1) - i8_to_int(old0);
    let newlen: int = i8_to_int(new1) - i8_to_int(new0);
    // by requires old[0] != old[1], oldlen != 0
    proof {
        assert(oldlen != 0);
    }
    let scale_i: int = newlen / oldlen;
    let offset_i: int = (i8_to_int(old1) * i8_to_int(new0) - i8_to_int(old0) * i8_to_int(new1)) / oldlen;
    let scale: i8 = scale_i as i8;
    let offset: i8 = offset_i as i8;
    proof {
        // show the integer relations that satisfy the specification
        assert(i8_to_int(offset) as int == offset_i);
        assert(i8_to_int(scale) as int == scale_i);
        assert(i8_to_int(offset) + i8_to_int(scale) * i8_to_int(old0) == i8_to_int(new0));
        assert(i8_to_int(offset) + i8_to_int(scale) * i8_to_int(old1) == i8_to_int(new1));
        assert(i8_to_int(scale) == newlen / oldlen);
        assert(i8_to_int(offset) == (i8_to_int(old1) * i8_to_int(new0) - i8_to_int(old0) * i8_to_int(new1)) / oldlen);
    }
    (offset, scale)
}
// </vc-code>

}
fn main() {}