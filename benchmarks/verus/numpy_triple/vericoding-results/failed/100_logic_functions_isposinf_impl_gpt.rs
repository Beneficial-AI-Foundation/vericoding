// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): lemma restating is_pos_inf definition for rewriting */
proof fn lemma_is_pos_inf_def(x: i32)
    ensures
        is_pos_inf(x) == (x == 0x7f800000i32),
{
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
    /* code modified by LLM (iteration 3): use usize indices for exec, seq views for specs, and proper casts */
    let mut r: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            r.len() == i,
            forall|j: int| 0 <= j < i as int ==> r@[j] == is_pos_inf(x@[j]),
        decreases (x.len() as int) - (i as int)
    {
        let val_i = x[i];
        let b: bool = val_i == 0x7f800000i32;
        let old_len: usize = r.len();
        r.push(b);
        proof {
            assert(old_len == i);
            assert(r@[old_len as int] == b);
            lemma_is_pos_inf_def(x@[old_len as int]);
            assert(r@[old_len as int] == is_pos_inf(x@[old_len as int]));
            assert forall|j: int|
                0 <= j < r.len() as int ==> r@[j] == is_pos_inf(x@[j])
            by {
                if j < old_len as int {
                    // follows from loop invariant (with i == old_len) and properties of push preserving prefix
                } else {
                    assert(j == old_len as int);
                    lemma_is_pos_inf_def(x@[old_len as int]);
                    assert(r@[j] == is_pos_inf(x@[j]));
                }
            }
        }
        i = i + 1;
    }
    r
}
// </vc-code>


}
fn main() {}