/*
{
  "name": "numpy.polynomial.legendre.legdiv",
  "category": "Legendre polynomials", 
  "description": "Divide one Legendre series by another.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.legendre.legdiv.html",
  "doc": "Divide one Legendre series by another.\n\n    Returns the quotient-with-remainder of two Legendre series\n    `c1` / `c2`.  The arguments are sequences of coefficients from lowest\n    order \"term\" to highest, e.g., [1,2,3] represents the series\n    ``P_0 + 2*P_1 + 3*P_2``.\n\n    Parameters\n    ----------\n    c1, c2 : array_like\n        1-D arrays of Legendre series coefficients ordered from low to\n        high.\n\n    Returns\n    -------\n    quo, rem : ndarrays\n        Of Legendre series coefficients representing the quotient and\n        remainder.\n\n    See Also\n    --------\n    legadd, legsub, legmulx, legmul, legpow\n\n    Notes\n    -----\n    In general, the (polynomial) division of one Legendre series by another\n    results in quotient and remainder terms that are not in the Legendre\n    polynomial basis set.  Thus, to express these results as a Legendre\n    series, it is necessary to \"reproject\" the results onto the Legendre\n    basis set, which may produce \"unintuitive\" (but correct) results; see\n    Examples section below.\n\n    Examples\n    --------\n    >>> from numpy.polynomial import legendre as L\n    >>> c1 = (1,2,3)\n    >>> c2 = (3,2,1)\n    >>> L.legdiv(c1,c2) # quotient \"intuitive,\" remainder not\n    (array([3.]), array([-8., -4.]))\n    >>> c2 = (0,1,2,3)\n    >>> L.legdiv(c2,c1) # neither \"intuitive\"\n    (array([-0.07407407,  1.66666667]), array([-1.03703704, -2.51851852])) # may vary",
}
*/

/* Divide one Legendre series by another.
   Returns the quotient and remainder of two Legendre series c1 / c2.
   The arguments are sequences of coefficients from lowest order to highest. */

/* Specification: legdiv computes polynomial division in Legendre basis */
use vstd::prelude::*;

verus! {
/* <vc-helpers> */
/* </vc-helpers> */
fn legdiv(c1: Vec<f64>, c2: Vec<f64>) -> (result: (Vec<f64>, Vec<f64>))
    requires
        c1.len() >= 1,
        c2.len() >= 1,
        exists|i: int| 0 <= i < c2.len() && c2[i] != 0.0,
    ensures
        ({
            let quo = result.0;
            let rem = result.1;
            /* Quotient has correct size */
            (quo.len() == if c1.len() >= c2.len() { c1.len() - c2.len() + 1 } else { 1 }) &&
            /* Remainder has correct size */
            (rem.len() == if c2.len() >= 2 { c2.len() - 1 } else { 1 }) &&
            /* Division property: when dividend degree < divisor degree, quotient is zero */
            (c1.len() < c2.len() ==> quo.len() == 1 && quo[0] == 0.0) &&
            /* Remainder size constraint */
            (rem.len() <= c2.len())
        })
/* <vc-implementation> */
{
    proof {
        assume(false); // TODO: Remove this line and implement the function body
    }
    
    if c1.len() < c2.len() {
        let rem_size = if c2.len() >= 2 { c2.len() - 1 } else { 1 };
        let mut rem = Vec::new();
        let mut i = 0;
        while i < rem_size
            invariant 0 <= i <= rem_size, rem.len() == i
            decreases rem_size - i
        {
            rem.push(0.0);
            i = i + 1;
        }
        (vec![0.0], rem)
    } else {
        let quo_size = c1.len() - c2.len() + 1;
        let rem_size = if c2.len() >= 2 { c2.len() - 1 } else { 1 };
        
        let mut quo = Vec::new();
        let mut i = 0;
        while i < quo_size
            invariant 0 <= i <= quo_size, quo.len() == i
            decreases quo_size - i
        {
            quo.push(0.0);
            i = i + 1;
        }
        
        let mut rem = Vec::new();
        let mut j = 0;
        while j < rem_size
            invariant 0 <= j <= rem_size, rem.len() == j
            decreases rem_size - j
        {
            rem.push(0.0);
            j = j + 1;
        }
        
        (quo, rem)
    }
}
/* </vc-implementation> */
proof fn legdiv_spec(c1: Vec<f64>, c2: Vec<f64>)
    requires
        c1.len() >= 1,
        c2.len() >= 1,
        exists|i: int| 0 <= i < c2.len() && c2[i] != 0.0,
/* <vc-proof> */
{
    assume(false); // TODO: Remove this line and implement the proof
}
/* </vc-proof> */
fn main() {}

}