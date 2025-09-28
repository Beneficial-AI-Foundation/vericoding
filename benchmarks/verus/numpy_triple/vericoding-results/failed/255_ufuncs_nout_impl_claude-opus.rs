// <vc-preamble>
use vstd::prelude::*;

verus! {

/* Represents a universal function (ufunc) type that captures basic metadata about 
   the number of inputs and outputs. In NumPy, this would be the ufunc object itself. */
struct UFunc {
    /* Number of input arguments the ufunc accepts */
    nin: nat,
    /* Number of output arguments the ufunc produces */
    nout_val: nat,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Convert nat to u8 safely */
spec fn nat_to_u8_spec(n: nat) -> u8
    recommends n <= u8::MAX as nat
{
    if n <= u8::MAX as nat {
        n as u8
    } else {
        u8::MAX
    }
}
// </vc-helpers>

// <vc-spec>
fn nout(ufunc: UFunc) -> (result: u8)
    requires ufunc.nout_val >= 1,
    ensures 
        result as nat == ufunc.nout_val,
        result as nat >= 1
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Use spec function for comparison in ghost context */
    assert(ufunc.nout_val >= 1);
    proof {
        assert(ufunc.nout_val <= u8::MAX as nat || ufunc.nout_val > u8::MAX as nat);
    }
    if ufunc.nout_val.as_usize() <= u8::MAX as usize {
        ufunc.nout_val.as_usize() as u8
    } else {
        u8::MAX
    }
}
// </vc-code>


}
fn main() {}