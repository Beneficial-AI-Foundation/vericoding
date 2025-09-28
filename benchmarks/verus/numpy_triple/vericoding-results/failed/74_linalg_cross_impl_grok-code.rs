// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_linalg_cross(x1: [i8; 3], x2: [i8; 3]) -> (result: [i8; 3])
    ensures
        result[0] as int == x1[1] as int * x2[2] as int - x1[2] as int * x2[1] as int,
        result[1] as int == x1[2] as int * x2[0] as int - x1[0] as int * x2[2] as int,
        result[2] as int == x1[0] as int * x2[1] as int - x1[1] as int * x2[0] as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed truncate attribute by adding parentheses around casts */
    let x1_0 = x1[0] as i32;
    let x1_1 = x1[1] as i32;
    let x1_2 = x1[2] as i32;
    let x2_0 = x2[0] as i32;
    let x2_1 = x2[1] as i32;
    let x2_2 = x2[2] as i32;
    let r0 = x1_1 * x2_2 - x1_2 * x2_1;
    let r1 = x1_2 * x2_0 - x1_0 * x2_2;
    let r2 = x1_0 * x2_1 - x1_1 * x2_0;
    let result = [
        #[verifier::truncate] (r0 as i8),
        #[verifier::truncate] (r1 as i8),
        #[verifier::truncate] (r2 as i8),
    ];
    result
}
// </vc-code>


}
fn main() {}