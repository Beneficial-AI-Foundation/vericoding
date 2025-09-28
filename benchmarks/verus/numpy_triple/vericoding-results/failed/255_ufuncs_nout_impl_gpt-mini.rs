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
/* helper modified by LLM (iteration 5): construct u8 equal to a nat <= 255 by recursion */
spec fn lemma_nat_to_u8_eq(n: nat) -> (r: u8)
    requires
        n <= 255,
    ensures
        (r as nat) == n,
    decreases
        n
{
    if n == 0 {
        0u8
    } else {
        let prev: u8 = lemma_nat_to_u8_eq(n - 1);
        prev + 1u8
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
    /* code modified by LLM (iteration 5): convert ufunc.nout_val to u8 via spec lemma */
    let res: u8 = lemma_nat_to_u8_eq(ufunc.nout_val);
    res
}
// </vc-code>


}
fn main() {}