// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added verus_algebraic_divide_to_i8 helper function */
proof fn lemma_div_by_sub(a_int: int, b_int: int, c_int: int, d_int: int)
    requires
        a_int != b_int,
        c_int * (a_int - b_int) == d_int,
    ensures
        d_int / (a_int - b_int) == c_int,
{
    assert((a_int - b_int) * c_int == d_int) by (nonlinear_arith);
}

fn verus_algebraic_divide_to_i8(val: int) -> (result: i8)
    requires
        0 <= val,
        val <= 127,
    ensures
        result as int == val,
{
    val as i8
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
/* code modified by LLM (iteration 5): removed int casting for real integers and fixed verus_algebraic_divide_to_i8 method call */
{
    let old0_int = old[0] as int;
    let old1_int = old[1] as int;
    let new0_int = new[0] as int;
    let new1_int = new[1] as int;

    let oldlen: int = old1_int - old0_int;
    let newlen: int = new1_int - new0_int;

    let scale_num: int = newlen;
    let scale_den: int = oldlen;

    let scale_val_int: int = scale_num / scale_den;

    proof {
        lemma_div_by_sub(old1_int, old0_int, scale_val_int, newlen);
    }

    let offset_num: int = old1_int * new0_int - old0_int * new1_int;
    let offset_den: int = oldlen;
    let offset_val_int: int = offset_num / offset_den;

    proof {
        lemma_div_by_sub(old1_int, old0_int, offset_val_int, offset_num);
    }

    let scale: i8 = verus_algebraic_divide_to_i8(scale_val_int);
    let offset: i8 = verus_algebraic_divide_to_i8(offset_val_int);

    (offset, scale)
}
// </vc-code>

}
fn main() {}