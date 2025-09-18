// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix compilation errors by moving integer arithmetic to proof context */
proof fn linear_equation_solution(a: i32, b: i32, c: i32, d: i32)
    requires a != b,
    ensures ({
        let oldlen = (b as int) - (a as int);
        let scale = ((d as int) - (c as int)) / oldlen;
        let offset = ((b as int) * (c as int) - (a as int) * (d as int)) / oldlen;
        offset + scale * (a as int) == (c as int) && offset + scale * (b as int) == (d as int)
    })
{
    let oldlen = (b as int) - (a as int);
    let scale = ((d as int) - (c as int)) / oldlen;
    let offset = ((b as int) * (c as int) - (a as int) * (d as int)) / oldlen;
    
    assert((b as int) * (c as int) - (a as int) * (d as int) + ((d as int) - (c as int)) * (a as int) == (c as int) * oldlen) by (nonlinear_arith);
    assert((b as int) * (c as int) - (a as int) * (d as int) + ((d as int) - (c as int)) * (b as int) == (d as int) * oldlen) by (nonlinear_arith);
    
    assert(offset + scale * (a as int) == ((b as int) * (c as int) - (a as int) * (d as int)) / oldlen + ((d as int) - (c as int)) * (a as int) / oldlen) by (nonlinear_arith);
    assert(offset + scale * (a as int) == ((b as int) * (c as int) - (a as int) * (d as int) + ((d as int) - (c as int)) * (a as int)) / oldlen) by (nonlinear_arith);
    assert(offset + scale * (a as int) == (c as int) * oldlen / oldlen) by (nonlinear_arith);
    assert(offset + scale * (a as int) == (c as int)) by (nonlinear_arith);
    
    assert(offset + scale * (b as int) == ((b as int) * (c as int) - (a as int) * (d as int)) / oldlen + ((d as int) - (c as int)) * (b as int) / oldlen) by (nonlinear_arith);
    assert(offset + scale * (b as int) == ((b as int) * (c as int) - (a as int) * (d as int) + ((d as int) - (c as int)) * (b as int)) / oldlen) by (nonlinear_arith);
    assert(offset + scale * (b as int) == (d as int) * oldlen / oldlen) by (nonlinear_arith);
    assert(offset + scale * (b as int) == (d as int)) by (nonlinear_arith);
}
// </vc-helpers>

// <vc-spec>
fn mapparms(old: [i32; 2], new: [i32; 2]) -> (result: (i32, i32))
    requires old[0] != old[1],
    ensures ({
        let (offset, scale) = result;
        let oldlen = old[1] - old[0];
        let newlen = new[1] - new[0];
        offset + scale * old[0] == new[0] &&
        offset + scale * old[1] == new[1] &&
        scale == newlen / oldlen &&
        offset == (old[1] * new[0] - old[0] * new[1]) / oldlen
    })
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): avoid int usage in executable code by performing calculations as i32 */
{
    let oldlen = old[1] - old[0];
    let newlen = new[1] - new[0];
    let scale = newlen / oldlen;
    let offset = (old[1] * new[0] - old[0] * new[1]) / oldlen;
    
    proof {
        linear_equation_solution(old[0], old[1], new[0], new[1]);
    }
    
    (offset, scale)
}
// </vc-code>

}
fn main() {}