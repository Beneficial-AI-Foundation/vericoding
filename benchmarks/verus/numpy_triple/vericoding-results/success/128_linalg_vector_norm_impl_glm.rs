// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn abs_i8(x: i8) -> (result: i8)
    ensures 
        result >= 0,
        x == -128 ==> result == 127,
        x != -128 ==> (x >= 0 ==> result == x) && (x < 0 ==> result == -x),
{
    if x >= 0 {
        x
    } else {
        if x == -128 {
            127
        } else {
            -x
        }
    }
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
    /* code modified by LLM (iteration 4): fixed vector indexing by using direct bounds in loops */
    if x.len() == 0 {
        0
    } else {
        if p == 0 {
            let mut count: i8 = 0;
            for i in 0..x.len()
                invariant 0 <= count <= 127,
            {
                if x[i] != 0 {
                    if count < 127 {
                        count += 1;
                    }
                }
            }
            count
        } else {
            let mut max_abs: i8 = 0;
            for i in 0..x.len()
                invariant 0 <= max_abs <= 127,
            {
                let abs_val = abs_i8(x[i]);
                if abs_val > max_abs {
                    max_abs = abs_val;
                }
            }
            max_abs
        }
    }
}
// </vc-code>

}
fn main() {}