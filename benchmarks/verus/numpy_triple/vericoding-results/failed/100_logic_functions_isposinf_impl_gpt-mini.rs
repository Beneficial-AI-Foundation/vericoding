// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): positive infinity implies not NaN */
fn lemma_posinf_not_nan(x: i32)
    ensures
        is_pos_inf(x) ==> !is_nan(x),
{
    proof {
        if is_pos_inf(x) {
            // Positive infinity has the exponent bits all ones and zero mantissa
            assert(x == 0x7f800000i32);
            assert((x & 0x7fffffi32) == 0);
            assert(!is_nan(x));
        }
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
{
    /* code modified by LLM (iteration 5): compute positive-infinity test without calling spec function */
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0usize;
    while i < x.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result[j] == is_pos_inf(x[j]),
        decreases x.len() - i
    {
        let xi: i32 = x[i];
        let ri: bool = xi == 0x7f800000i32;
        result.push(ri);
        proof {
            assert(result.len() == i + 1usize);
            assert(result[i as int] == ri);
            assert(ri == (xi == 0x7f800000i32));
            if ri {
                lemma_posinf_not_nan(xi);
            }
        }
        i = i + 1usize;
    }
    result
}
// </vc-code>


}
fn main() {}