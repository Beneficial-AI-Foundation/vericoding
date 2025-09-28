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
/* helper modified by LLM (iteration 5): recursive conversion from nat to u8 */
fn u8_of_nat(n: nat) -> (result: u8)
    ensures
        result as nat == n,
    decreases
        n,
{
    if n == 0 {
        0u8
    } else {
        let r: u8 = u8_of_nat(n - 1);
        let res: u8 = r + 1u8;
        proof {
            assert(r as nat == n - 1);
            assert((r as nat) + 1 == n);
        }
        res
    }
}

// </vc-helpers>

// <vc-spec>
fn numpy_nargs(ufunc: Ufunc) -> (result: u8)
    ensures result as nat == ufunc.nin + ufunc.nout
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute sum and convert to u8 */
    let sum: nat = ufunc.nin + ufunc.nout;
    let result: u8 = u8_of_nat(sum);
    result
}

// </vc-code>


}
fn main() {}