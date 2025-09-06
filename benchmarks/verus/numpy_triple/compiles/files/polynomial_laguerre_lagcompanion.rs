/* 
{
  "name": "numpy.polynomial.laguerre.lagcompanion",
  "category": "Laguerre polynomials",
  "description": "Return the companion matrix of c.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.laguerre.lagcompanion.html",
  "doc": "Return the companion matrix of c.\n\n    The usual companion matrix of the Laguerre polynomials is already\n    symmetric when `c` is a basis Laguerre polynomial, so no scaling is\n    applied.\n\n    Parameters\n    ----------\n    c : array_like\n        1-D array of Laguerre series coefficients ordered from low to high\n        degree.\n\n    Returns\n    -------\n    mat : ndarray\n        Companion matrix of dimensions (deg, deg).\n\n    Examples\n    --------\n    >>> from numpy.polynomial.laguerre import lagcompanion\n    >>> lagcompanion([1, 2, 3])\n    array([[ 1.        , -0.33333333],\n           [-1.        ,  4.33333333]])",
}
*/

/* Returns the companion matrix of Laguerre polynomial coefficients.
   The companion matrix is a square matrix of size (deg, deg) where deg = c.size - 1.
   For coefficients [c₀, c₁, ..., cₙ], the companion matrix has specific structure
   for Laguerre polynomials with diagonal elements 2*i + 1 and off-diagonal elements. */

/* Specification: lagcompanion returns the companion matrix of Laguerre polynomial coefficients.
   The companion matrix is symmetric for Laguerre polynomials and has dimension (deg, deg)
   where deg = c.size - 1. The matrix structure follows the Laguerre polynomial recurrence relation. */
use vstd::prelude::*;

verus! {
/* <vc-helpers> */
/* </vc-helpers> */
fn lagcompanion(c: Vec<f64>) -> (result: Vec<Vec<f64>>)
    requires c.len() >= 2
/* <vc-implementation> */
{
    return Vec::new(); // TODO: Remove this line and implement the function body
}
/* </vc-implementation> */
proof fn lagcompanion_spec(c: Vec<f64>) 
    requires c.len() >= 2
/* <vc-proof> */
{
    assume(false); // TODO: Remove this line and implement the proof
}
/* </vc-proof> */
fn main() {}

}