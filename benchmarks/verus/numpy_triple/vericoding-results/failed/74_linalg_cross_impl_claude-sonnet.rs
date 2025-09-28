// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): direct computation without helper to avoid overflow issues */
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
    /* code modified by LLM (iteration 5): direct computation using int arithmetic and explicit bounds checking */
    let r0_int = x1[1] as int * x2[2] as int - x1[2] as int * x2[1] as int;
    let r1_int = x1[2] as int * x2[0] as int - x1[0] as int * x2[2] as int;
    let r2_int = x1[0] as int * x2[1] as int - x1[1] as int * x2[0] as int;
    
    proof {
        assert(-128 <= r0_int <= 127);
        assert(-128 <= r1_int <= 127);
        assert(-128 <= r2_int <= 127);
    }
    
    let r0 = r0_int as i8;
    let r1 = r1_int as i8;
    let r2 = r2_int as i8;
    
    [r0, r1, r2]
}
// </vc-code>


}
fn main() {}