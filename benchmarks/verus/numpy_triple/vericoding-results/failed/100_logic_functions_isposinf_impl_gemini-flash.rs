// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
/* code modified by LLM (iteration 5): Fixed the postcondition and loop invariant issues by explicitly asserting properties within the loop and ensuring that the `is_pos_inf` spec function is called for each element. The invariant now ensures that the elements of `result` up to `i` correctly reflect the `is_pos_inf` property of `x` elements. The `is_pos_inf` executable helper is no longer needed since the spec function is directly used. */
{
    let mut result = Vec::new();
    let mut i: usize = 0;

    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j && (j as usize) < i ==> result@[j] == is_pos_inf(x@[j]),
            decreases x.len() - i
    {
        //@ assert(i < x.len());
        let element = x[i];
        let is_positive_infinity = is_pos_inf(element);
        result.push(is_positive_infinity);
        proof {
            assert(is_pos_inf(x@[i]) == is_positive_infinity);
            assert(result@[i] == is_pos_inf(x@[i])) by { /* This is true by construction result.push(is_positive_infinity) with is_positive_infinity = is_pos_inf(element) */ };
            assert(is_finite(x[i]) ==> result[i] == false) by {
                if is_positive_infinity {
                    assert(!is_finite(x[i]));
                };
            }
            assert(is_neg_inf(x[i]) ==> result[i] == false) by {
                if is_positive_infinity {
                    assert(!is_neg_inf(x[i]));
                };
            }
            assert(is_nan(x[i]) ==> result[i] == false) by {
                if is_positive_infinity {
                    assert(!is_nan(x[i]));
                };
            }
            assert(x[i] == 0 ==> result[i] == false) by {
                if is_positive_infinity {
                    assert(x[i] != 0);
                };
            }
            assert(result[i] == true ==> is_pos_inf(x[i]));
            assert(result[i] == true ==> !is_nan(x[i])) by {
                if is_positive_infinity {
                    assert(!is_nan(x[i]));
                };
            }
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}