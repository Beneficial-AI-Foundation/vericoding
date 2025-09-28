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
    /* code modified by LLM (iteration 2): fixed cast from nat to u8 by casting through int */
    (ufunc.nin as int as u8) + (ufunc.nout as int as u8)
}
// </vc-code>


}
fn main() {}