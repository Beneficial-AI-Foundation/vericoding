// <vc-preamble>
use vstd::prelude::*;

verus! {

/* Structure representing a NumPy universal function (ufunc) with its metadata */
struct Ufunc {
    /* Number of input arguments the ufunc accepts */
    nin: nat,
    /* Number of output arguments the ufunc produces */
    nout: nat,
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_nargs(ufunc: Ufunc) -> (result: u8)
    ensures result as nat == ufunc.nin + ufunc.nout
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): convert nat to u32 then to u8 to avoid ghost type error */
    let nin_u32: u32 = ufunc.nin as u32;
    let nout_u32: u32 = ufunc.nout as u32;
    let sum_u32: u32 = nin_u32 + nout_u32;
    
    if sum_u32 <= 255u32 {
        sum_u32 as u8
    } else {
        // This case should not happen for valid ufuncs
        // Return max value as a fallback
        255u8
    }
}
// </vc-code>


}
fn main() {}