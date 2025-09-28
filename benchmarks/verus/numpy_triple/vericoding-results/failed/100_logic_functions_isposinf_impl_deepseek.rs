// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helpers modified by LLM (iteration 5): Added vector indexing helper and improved lemma specifications */

proof fn lemma_finite_not_pos_inf(x: i32)
    requires
        is_finite(x),
    ensures
        !is_pos_inf(x)
{
    assert(is_finite(x) == ((x & 0x7f800000i32) != 0x7f800000i32));
    assert(is_pos_inf(x) == (x == 0x7f800000i32));
}

proof fn lemma_nan_check(x: i32)
    ensures
        is_nan(x) ==> !is_pos_inf(x)
{
    assert(is_nan(x) == ((x & 0x7f800000i32) == 0x7f800000i32 && (x & 0x7fffffi32) != 0));
    assert(is_pos_inf(x) == (x == 0x7f800000i32));
}

proof fn lemma_zero_not_inf(x: i32)
    ensures
        x == 0 ==> !is_pos_inf(x)
{
    assert(0 != 0x7f800000i32);
}

proof fn lemma_neg_inf_check(x: i32)
    ensures
        is_neg_inf(x) ==> !is_pos_inf(x)
{
    assert(is_neg_inf(x) == (x == 0xff800000u32 as i32));
    assert(0xff800000u32 as i32 == 0xff800000i32);
    assert(0xff800000i32 != 0x7f800000i32);
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
/* code modified by LLM (iteration 5): Fixed vector access using seq() method and proper indexing */
{
    let mut result = Vec::new();
    let n = x.len();
    let mut i = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                result@[j] == is_pos_inf(x@[j]) &&
                (is_finite(x@[j]) ==> result@[j] == false) &&
                (is_neg_inf(x@[j]) ==> result@[j] == false) &&
                (is_nan(x@[j]) ==> result@[j] == false) &&
                (x@[j] == 0 ==> result@[j] == false) &&
                (result@[j] == true ==> is_pos_inf(x@[j])) &&
                (result@[j] == true ==> !is_nan(x@[j]))
            },
        decreases n - i
    {
        let element = x@[i];
        let is_pos_inf_val = element == 0x7f800000i32;
        
        lemma_finite_not_pos_inf(element);
        lemma_nan_check(element);
        lemma_neg_inf_check(element);
        lemma_zero_not_inf(element);
        
        result.push(is_pos_inf_val);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}