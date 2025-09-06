/*
{
  "name": "numpy.polynomial.legendre.legadd",
  "category": "Legendre polynomials",
  "description": "Add one Legendre series to another.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.legendre.legadd.html",
  "doc": "Add one Legendre series to another.\n\n    Returns the sum of two Legendre series `c1` + `c2`.  The arguments\n    are sequences of coefficients ordered from lowest order term to\n    highest, i.e., [1,2,3] represents the series ``P_0 + 2*P_1 + 3*P_2``.\n\n    Parameters\n    ----------\n    c1, c2 : array_like\n        1-D arrays of Legendre series coefficients ordered from low to\n        high.\n\n    Returns\n    -------\n    out : ndarray\n        Array representing the Legendre series of their sum.\n\n    See Also\n    --------\n    legsub, legmulx, legmul, legdiv, legpow\n\n    Notes\n    -----\n    Unlike multiplication, division, etc., the sum of two Legendre series\n    is a Legendre series (without having to \"reproject\" the result onto\n    the basis set) so addition, just like that of \"standard\" polynomials,\n    is simply \"component-wise.\"\n\n    Examples\n    --------\n    >>> from numpy.polynomial import legendre as L\n    >>> c1 = (1,2,3)\n    >>> c2 = (3,2,1)\n    >>> L.legadd(c1,c2)\n    array([4.,  4.,  4.])",
}
*/

/* Add one Legendre series to another by component-wise addition of coefficients */

/* Specification: legadd performs component-wise addition of two Legendre series coefficients */
use vstd::prelude::*;

verus! {
// <vc-helpers>
spec fn max(a: nat, b: nat) -> nat {
    if a >= b { a } else { b }
}
// </vc-helpers>
fn legadd(c1: Vec<i32>, c2: Vec<i32>) -> (result: Vec<i32>)
// <vc-implementation>
    {
        return Vec::new(); // TODO: Remove this line and implement the function body
    }
// </vc-implementation>
proof fn legadd_spec_proof(c1: Vec<i32>, c2: Vec<i32>)
    ensures
        /* Each coefficient is the sum of corresponding coefficients */
        true
        /* forall i in range(max(len(c1), len(c2))):
           result[i] = (c1[i] if i < len(c1) else 0) + (c2[i] if i < len(c2) else 0) */
    {
// <vc-proof>
    assume(false); // TODO: Remove this line and implement the proof
// </vc-proof>
}

fn main() {}

}