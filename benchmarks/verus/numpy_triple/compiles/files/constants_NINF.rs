/*
{
  "name": "numpy.NINF",
  "category": "Special float values (deprecated)",
  "description": "IEEE 754 floating point representation of negative infinity",
  "url": "https://numpy.org/doc/stable/reference/constants.html",
  "doc": "IEEE 754 floating point representation of negative infinity.\n\nDEPRECATED: Removed from main namespace in NumPy 2.0. Use -np.inf instead.",
}
*/

/* IEEE 754 floating point representation of negative infinity (deprecated in NumPy 2.0) */

/* Specification: NINF represents negative infinity with the following properties:
   1. NINF is less than any finite float value
   2. NINF + any finite value = NINF
   3. NINF * positive finite value = NINF
   4. NINF * negative finite value = inf
   5. NINF / any finite non-zero value = NINF (with appropriate sign)
   6. NINF = -inf (negative of positive infinity) */
use vstd::prelude::*;

verus! {
/* <vc-helpers> */
/* </vc-helpers> */
spec fn NINF() -> i64 {
  i64::MIN
}

fn exec_NINF() -> i64
/* <vc-implementation> */
{
    return i64::MIN; // TODO: Remove this line and implement the function body
}
/* </vc-implementation> */
proof fn NINF_spec() 
    ensures
        /* Basic properties of NINF as minimum integer value */
        NINF() == i64::MIN &&
        NINF() < 0
/* <vc-proof> */
{
    assume(false); // TODO: Remove this line and implement the proof
}
/* </vc-proof> */
fn main() {
}

}