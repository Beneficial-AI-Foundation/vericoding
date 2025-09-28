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
/* helper modified by LLM (iteration 5): conversion function from nat to u8 with bounds checking */
fn nat_to_u8(n: nat) -> (result: u8)
    requires n <= 255,
    ensures result as nat == n
{
    n as u8
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
    /* code modified by LLM (iteration 5): use helper function for nat to u8 conversion */
    nat_to_u8(ufunc.nout_val)
}
// </vc-code>


}
fn main() {}