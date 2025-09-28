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
/* helper modified by LLM (iteration 5): added nat_to_u8 helper function to safely convert nat to u8 without casts */
fn nat_to_u8(n: nat) -> (result: u8)
	decreases n,
	requires n <= 255,
	ensures result as nat == n,
{
	if n == 0 {
		0u8
	} else {
		nat_to_u8(n - 1) + 1u8
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
	/* code modified by LLM (iteration 5): added assertion for range and used helper function for nat to u8 conversion */
	proof {
		assert(ufunc.nout_val <= 255);
	}
	let result = nat_to_u8(ufunc.nout_val);
	result
}
// </vc-code>


}
fn main() {}