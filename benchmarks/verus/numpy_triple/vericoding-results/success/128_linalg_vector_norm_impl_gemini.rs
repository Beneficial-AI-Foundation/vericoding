// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn int_abs(i: int) -> int {
    if i < 0 { -i } else { i }
}

spec fn spec_i8_abs(x: i8) -> int {
    if x == i8::MIN { i8::MAX as int } else { int_abs(x as int) }
}

fn i8_abs(x: i8) -> (res: i8)
    ensures
        res >= 0,
        res as int == spec_i8_abs(x),
{
    if x < 0 {
        if x == i8::MIN {
            i8::MAX
        } else {
            -x
        }
    } else {
        x
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
    /* code modified by LLM (iteration 4): Added invariant to prove postcondition for empty vector. */
    let mut max_norm: i8 = 0;
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            max_norm >= 0,
            i == 0 ==> max_norm == 0,
            forall|j: int| 0 <= j < i ==> (max_norm as int) >= spec_i8_abs(x@[j]),
        decreases x.len() - i
    {
        let val = x[i];
        let abs_val = i8_abs(val);
        if abs_val > max_norm {
            max_norm = abs_val;
        }
        i = i + 1;
    }
    max_norm
}
// </vc-code>

}
fn main() {}