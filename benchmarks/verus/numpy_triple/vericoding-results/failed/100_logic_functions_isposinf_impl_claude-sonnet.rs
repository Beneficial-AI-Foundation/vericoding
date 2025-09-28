// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed value calculations and bit operations */
proof fn pos_inf_not_neg_inf(x: i32)
    requires x == 0x7f800000i32
    ensures x != (#[verifier::truncate] 0xff800000u32 as i32)
{
    assert(0x7f800000i32 != (#[verifier::truncate] 0xff800000u32 as i32));
}

proof fn pos_inf_not_nan(x: i32)
    requires x == 0x7f800000i32
    ensures !is_nan(x)
{
    assert((x & 0x7f800000i32) == 0x7f800000i32);
    assert((x & 0x007fffffi32) == 0);
    assert(!((x & 0x7f800000i32) == 0x7f800000i32 && (x & 0x007fffffi32) != 0));
}

proof fn neg_inf_not_pos_inf(x: i32)
    requires x == (#[verifier::truncate] 0xff800000u32 as i32)
    ensures x != 0x7f800000i32
{
    assert((#[verifier::truncate] 0xff800000u32 as i32) != 0x7f800000i32);
}

proof fn nan_not_pos_inf(x: i32)
    requires is_nan(x)
    ensures x != 0x7f800000i32
{
    assert((x & 0x007fffffi32) != 0);
    assert(x != 0x7f800000i32);
}
// </vc-helpers>

// <vc-spec>
spec fn is_pos_inf(x: i32) -> bool {
    x == 0x7f800000i32
}

spec fn is_neg_inf(x: i32) -> bool {
    x == 0xff800000u32 as i32
}

spec fn is_nan(x: i32) -> bool {
    (x & 0x7f800000i32) == 0x7f800000i32 && (x & 0x7fffffi32) != 0
}

spec fn is_finite(x: i32) -> bool {
    (x & 0x7f800000i32) != 0x7f800000i32
}

fn isposinf(x: Vec<i32>) -> (result: Vec<bool>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> {
            /* Primary property: result is true iff input is positive infinity */
            result[i] == is_pos_inf(x[i]) &&
            /* Sanity checks: finite values return false */
            (is_finite(x[i]) ==> result[i] == false) &&
            /* Negative infinity returns false */
            (is_neg_inf(x[i]) ==> result[i] == false) &&
            /* NaN is not positive infinity */
            (is_nan(x[i]) ==> result[i] == false) &&
            /* Zero is not positive infinity */
            (x[i] == 0 ==> result[i] == false) &&
            /* Mathematical property: if result is true, then x is positive infinity */
            (result[i] == true ==> is_pos_inf(x[i])) &&
            /* Exclusivity: cannot be both positive infinity and NaN */
            (result[i] == true ==> !is_nan(x[i]))
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): simplified implementation to match spec */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                result[j] == is_pos_inf(x[j]) &&
                (is_finite(x[j]) ==> result[j] == false) &&
                (is_neg_inf(x[j]) ==> result[j] == false) &&
                (is_nan(x[j]) ==> result[j] == false) &&
                (x[j] == 0 ==> result[j] == false) &&
                (result[j] == true ==> is_pos_inf(x[j])) &&
                (result[j] == true ==> !is_nan(x[j]))
            }
        decreases x.len() - i
    {
        let is_pos_inf_val = x[i] == 0x7f800000i32;
        result.push(is_pos_inf_val);
        
        proof {
            assert(result[i as int] == is_pos_inf(x[i as int]));
            
            if is_finite(x[i as int]) {
                assert((x[i as int] & 0x7f800000i32) != 0x7f800000i32);
                assert(result[i as int] == false);
            }
            
            if is_neg_inf(x[i as int]) {
                assert(result[i as int] == false);
            }
            
            if is_nan(x[i as int]) {
                assert(result[i as int] == false);
            }
            
            if x[i as int] == 0 {
                assert(result[i as int] == false);
            }
        }
        
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}