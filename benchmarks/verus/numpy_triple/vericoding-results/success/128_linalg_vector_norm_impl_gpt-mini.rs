// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): returns non-ghost i32 absolute value */
fn abs_i8_to_i32(a: i8) -> i32 {
    if a < 0 { -(a as i32) } else { a as i32 }
}
// </vc-helpers>

// <vc-spec>
fn vector_norm(x: Vec<i8>, p: i8) -> (result: i8)
    requires p as int >= 0,
    ensures 
        result as int >= 0,
        x@.len() == 0 ==> result as int == 0,
        result as int >= 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): compute max absolute value clamped to i8 */
    if x.len() == 0 {
        0 as i8
    } else {
        let mut max_abs: i32 = 0;
        let mut i: usize = 0;
        while i < x.len()
            invariant
                i <= x.len(),
                max_abs >= 0,
            decreases x.len() - i
        {
            let xi: i8 = x[i];
            let ai: i32 = abs_i8_to_i32(xi);
            if ai > max_abs {
                max_abs = ai;
            }
            i = i + 1;
        }
        if max_abs > 127 {
            127 as i8
        } else {
            max_abs as i8
        }
    }
}
// </vc-code>

}
fn main() {}