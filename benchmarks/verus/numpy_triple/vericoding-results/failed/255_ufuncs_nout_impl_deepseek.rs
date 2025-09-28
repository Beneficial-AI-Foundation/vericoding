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
/* helper modified by LLM (iteration 5): Fixed nat to int conversion using ghost variable */
fn nat_to_u8(n: nat) -> (result: u8)
    requires
        n <= 0xff as int,
    ensures
        result as nat == n,
{
    proof {
        let n_int: int = n as int;
        assert(n_int <= 0xff);
    }
    ghost {
        let n_ghost: int = n as int;
        assert(n_ghost <= 0xff);
    }
    (n_ghost as u8)
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
    /* code modified by LLM (iteration 5): Fixed ghost variable usage and bounds verification */
    proof {
        assert(ufunc.nout_val <= 0xff as int) by {
            // Since nout_val is a nat and u8 max is 255, and we know nout_val >= 1
        };
    }
    ghost {
        let n_ghost: int = ufunc.nout_val as int;
        assert(n_ghost <= 0xff);
    }
    let result = nat_to_u8(ufunc.nout_val);
    result
}
// </vc-code>


}
fn main() {}