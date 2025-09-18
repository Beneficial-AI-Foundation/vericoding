// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove division inverse for multiplication by 3 on i128 */
proof fn mul3_div_inverse_i128(x: i128)
    ensures
        (x * 3) / 3 == x,
        ((x * 3) / 3) * 3 == x * 3,
{
    assert((x * 3) / 3 == x);
    assert(((x * 3) / 3) * 3 == x * 3);
}

// </vc-helpers>

// <vc-spec>
fn triple(x: i32) -> (result: i32)
    ensures
        result / 3 == x,
        result / 3 * 3 == result,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute triple using i128 intermediate and prove properties */
    let tmp: i128 = (x as i128) * 3;
    assert(tmp >= (i32::MIN as i128) && tmp <= (i32::MAX as i128));
    let result: i32 = tmp as i32;
    proof {
        mul3_div_inverse_i128(x as i128);
        assert((tmp / 3) == x as i128);
        assert((result as i128) == tmp);
        assert((result as i128) / 3 == x as i128);
        assert(((result / 3) as i128) == (result as i128) / 3);
        assert((result / 3) == x);
        assert(((result / 3) as i128) * 3 == (result as i128));
        assert(((result / 3) * 3) == result);
    }
    result
}
// </vc-code>

}
fn main() {}