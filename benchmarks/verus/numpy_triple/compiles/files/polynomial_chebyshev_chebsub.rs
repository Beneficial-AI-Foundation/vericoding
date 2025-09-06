/* Subtract one Chebyshev series from another.

  Returns the difference of two Chebyshev series `c1` - `c2`.  The
  sequences of coefficients are from lowest order term to highest, i.e.,
  [1,2,3] represents the series ``T_0 + 2*T_1 + 3*T_2``.

  Parameters
  ----------
  c1, c2 : array_like
      1-D arrays of Chebyshev series coefficients ordered from low to
      high.

  Returns
  -------
  out : ndarray
      Of Chebyshev series coefficients representing their difference.

  See Also
  --------
  chebadd, chebmulx, chebmul, chebdiv, chebpow

  Notes
  -----
  Unlike multiplication, division, etc., the difference of two Chebyshev
  series is a Chebyshev series (without having to "reproject" the result
  onto the basis set) so subtraction, just like that of "standard"
  polynomials, is simply "component-wise."

  Examples
  --------
  >>> from numpy.polynomial import chebyshev as C
  >>> c1 = (1,2,3)
  >>> c2 = (3,2,1)
  >>> C.chebsub(c1,c2)
  array([-2.,  0.,  2.])
  >>> C.chebsub(c2,c1) # -C.chebsub(c1,c2)
  array([ 2.,  0., -2.])

Subtract one Chebyshev series from another component-wise.
    The input vectors c1 and c2 represent Chebyshev series coefficients
    ordered from lowest to highest degree term.

Specification: chebsub performs component-wise subtraction of two Chebyshev series.
    
    The specification includes:
    1. The basic property that each coefficient in the result is the difference
       of the corresponding coefficients in c1 and c2
    2. Anti-commutativity: chebsub(c1, c2) = -chebsub(c2, c1)
    3. Identity property: subtracting a series from itself yields zero
    4. Associativity with addition: (c1 - c2) + c2 = c1 */

use vstd::prelude::*;

verus! {
fn chebsub(c1: &Vec<f32>, c2: &Vec<f32>) -> (result: Vec<f32>)
    requires 
        c1.len() == c2.len(),
    ensures 
        result.len() == c1.len(),
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}