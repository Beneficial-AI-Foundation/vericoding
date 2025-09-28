// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed failing `by(bit_vector)` proofs to let the default SMT solver handle them */
fn isposinf_scalar(x: i32) -> (result: bool)
    ensures
        result == is_pos_inf(x),
        (is_finite(x) ==> result == false),
        (is_neg_inf(x) ==> result == false),
        (is_nan(x) ==> result == false),
        (x == 0 ==> result == false),
        (result == true ==> is_pos_inf(x)),
        (result == true ==> !is_nan(x)),
{
    if x == 0x7f800000i32 {
        proof {
            // Prove that x is not finite
            assert((x & 0x7f800000i32) == 0x7f800000i32);
            assert(!is_finite(x));
            
            // Prove that x is not negative infinity
            assert(x != 0xff800000u32 as i32);
            assert(!is_neg_inf(x));

            // Prove that x is not NaN
            assert((x & 0x7fffffi32) == 0);
            assert(!is_nan(x));

            // Prove that x is not 0
            assert(x != 0);
        }
        true
    } else {
        false
    }
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
/* code modified by LLM (iteration 5): no changes to logic, it correctly applies the helper function in a loop */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> {
                result@[j] == is_pos_inf(x@[j]) &&
                (is_finite(x@[j]) ==> result@[j] == false) &&
                (is_neg_inf(x@[j]) ==> result@[j] == false) &&
                (is_nan(x@[j]) ==> result@[j] == false) &&
                (x@[j] == 0 ==> result@[j] == false) &&
                (result@[j] == true ==> is_pos_inf(x@[j])) &&
                (result@[j] == true ==> !is_nan(x@[j]))
            },
        decreases x.len() - i
    {
        let b = isposinf_scalar(x[i]);
        result.push(b);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}