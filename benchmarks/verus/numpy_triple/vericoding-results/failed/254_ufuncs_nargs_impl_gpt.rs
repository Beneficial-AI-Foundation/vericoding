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
/* helper modified by LLM (iteration 5): roundtrip cast between nat and u8 when within bounds */
proof fn nat_u8_roundtrip(n: nat)
    requires
        n <= 255,
    ensures
        ((n as u8) as nat) == n,
{
}

/* helper modified by LLM (iteration 5): basic arithmetic properties used in reasoning */
proof fn sum_props(a: nat, b: nat, c: nat)
    ensures
        a + b == b + a,
        a + (b + c) == (a + b) + c,
{
}
// </vc-helpers>

// <vc-spec>
fn numpy_nargs(ufunc: Ufunc) -> (result: u8)
    ensures result as nat == ufunc.nin + ufunc.nout
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute total nargs as nin + nout and return as u8 */
    let total: nat = ufunc.nin + ufunc.nout;
    let r: u8 = total as u8;
    r
}
// </vc-code>


}
fn main() {}