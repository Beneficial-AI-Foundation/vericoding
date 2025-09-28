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
    /* code modified by LLM (iteration 2): use i32 for intermediate arithmetic to avoid int type in exec code */
    let x = ((x1[1] as i32) * (x2[2] as i32) - (x1[2] as i32) * (x2[1] as i32)) as i8;
    let y = ((x1[2] as i32) * (x2[0] as i32) - (x1[0] as i32) * (x2[2] as i32)) as i8;
    let z = ((x1[0] as i32) * (x2[1] as i32) - (x1[1] as i32) * (x2[0] as i32)) as i8;
    [x, y, z]
}
// </vc-code>


}
fn main() {}