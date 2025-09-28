// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No specific helpers needed, keeping this section empty. */
// </vc-helpers>

// <vc-spec>
fn numpy_bitwise_not(x: Vec<i8>) -> (result: Vec<i8>)
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == -(x[i] as int + 1)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type mismatch error by casting `x[j as int]` to `int` before using it in the assertion. */
{
    let mut result = Vec::new();
    let x_len = x.len();
    let mut i: usize = 0;

    while i < x_len
        invariant
            i <= x_len,
            result.len() == i,
            forall|j: int| 0 <= j && (j as usize) < i ==> result[j as usize] as int == -(x[j as usize] as int + 1),
    {
        let val_x: i8 = x[i];
        let val_res: i8 = -(val_x + 1);
        result.push(val_res);
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}