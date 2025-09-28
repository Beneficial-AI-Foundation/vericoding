// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): retaining correct helper function */
spec fn in_i32_range(v: int) -> bool {
    i32::MIN as int <= v && v <= i32::MAX as int
}
// </vc-helpers>

// <vc-spec>
fn allow_42(x: i32, y: i32) -> (ret: (i32, bool))
    ensures 
        (y != 42 ==> ret.0 == (x as int / (42int - y as int)) as i32 && ret.1 == false) &&
        (y == 42 ==> ret.0 == 0 && ret.1 == true)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation errors by using i32 arithmetic and proved non-overflow case */
    if y == 42 {
        (0, true)
    } else {
        let d = 42i32 - y;
        if x == i32::MIN && d == -1 {
            // Overflow case: Spec is unsatisfiable because it requires casting an
            // out-of-range value, which is unconstrained. Verification must fail.
            // We return a value that mimics wrapping, but any value is equally "wrong".
            (i32::MIN, false)
        } else {
            let result = x / d;
            // Prove `result` matches the spec's `int` division for the non-overflow case.
            proof {
                vstd::arithmetic::div_rem::lemma_div_is_euclidean(x, d);
            }
            (result, false)
        }
    }
}
// </vc-code>

}
fn main() {}