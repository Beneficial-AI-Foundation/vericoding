// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fix trigger annotation for quantifier */
fn is_pos_inf_exec(x: i32) -> (result: bool)
    ensures
        result == is_pos_inf(x)
{
    x == 0x7f800000i32
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
    /* code modified by LLM (iteration 5): Fix trigger annotation syntax */
    let mut result = Vec::with_capacity(x.len());
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                #[trigger] result[j] == #[trigger] is_pos_inf(x[j]) &&
                (is_finite(x[j]) ==> result[j] == false) &&
                (is_neg_inf(x[j]) ==> result[j] == false) &&
                (is_nan(x[j]) ==> result[j] == false) &&
                (x[j] == 0 ==> result[j] == false) &&
                (result[j] == true ==> is_pos_inf(x[j])) &&
                (result[j] == true ==> !is_nan(x[j]))
            }
        decreases x.len() - i
    {
        let val = x[i];
        let is_pos = is_pos_inf_exec(val);
        result.push(is_pos);
        proof {
            assert(is_pos == is_pos_inf(val));
        }
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}