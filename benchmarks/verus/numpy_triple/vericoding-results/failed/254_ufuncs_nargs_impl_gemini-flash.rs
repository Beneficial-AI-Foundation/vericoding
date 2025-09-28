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
/* code modified by LLM (iteration 5): Corrected type handling by using `as` for nat to u8 conversion, fixing `reveal_value` error and `nat` to integer comparison error. */
{
    let total_args = ufunc.nin + ufunc.nout;
    if total_args >= 256nat {
        255
    } else {
        total_args as u8
    }
}
// </vc-code>


}
fn main() {}