/- 
{
  "name": "numpy.polynomial.polynomial.polyvander2d",
  "category": "Standard polynomials",
  "description": "Pseudo-Vandermonde matrix of given degrees.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.polynomial.polyvander2d.html",
  "doc": "Pseudo-Vandermonde matrix of given degrees.\n\n    Returns the pseudo-Vandermonde matrix of degrees `deg` and sample\n    points ``(x, y)``. The pseudo-Vandermonde matrix is defined by\n\n    .. math:: V[..., (deg[1] + 1)*i + j] = x^i * y^j,\n\n    where ``0 <= i <= deg[0]`` and ``0 <= j <= deg[1]``. The leading indices of\n    `V` index the points ``(x, y)`` and the last index encodes the powers of\n    `x` and `y`.\n\n    If ``V = polyvander2d(x, y, [xdeg, ydeg])``, then the columns of `V`\n    correspond to the elements of a 2-D coefficient array `c` of shape\n    (xdeg + 1, ydeg + 1) in the order\n\n    .. math:: c_{00}, c_{01}, c_{02} ... , c_{10}, c_{11}, c_{12} ...\n\n    and ``np.dot(V, c.flat)`` and ``polyval2d(x, y, c)`` will be the same\n    up to roundoff. This equivalence is useful both for least squares\n    fitting and for the evaluation of a large number of 2-D polynomials\n    of the same degrees and sample points.\n\n    Parameters\n    ----------\n    x, y : array_like\n        Arrays of point coordinates, all of the same shape. The dtypes\n        will be converted to either float64 or complex128 depending on\n        whether any of the elements are complex. Scalars are converted to\n        1-D arrays.\n    deg : list of ints\n        List of maximum degrees of the form [x_deg, y_deg].\n\n    Returns\n    -------\n    vander2d : ndarray\n        The shape of the returned matrix is ``x.shape + (order,)``, where\n        :math:`order = (deg[0]+1)*(deg([1]+1)`.  The dtype will be the same\n        as the converted `x` and `y`.\n\n    See Also\n    --------\n    polyvander, polyvander3d, polyval2d, polyval3d\n\n    Examples\n    --------\n    >>> import numpy as np\n\n    The 2-D pseudo-Vandermonde matrix of degree ``[1, 2]`` and sample\n    points ``x = [-1, 2]`` and ``y = [1, 3]`` is as follows:\n\n    >>> from numpy.polynomial import polynomial as P\n    >>> x = np.array([-1, 2])\n    >>> y = np.array([1, 3])\n    >>> m, n = 1, 2\n    >>> deg = np.array([m, n])\n    >>> V = P.polyvander2d(x=x, y=y, deg=deg)\n    >>> V\n    array([[ 1.,  1.,  1., -1., -1., -1.],\n           [ 1.,  3.,  9.,  2.,  6., 18.]])\n\n    We can verify the columns for any ``0 <= i <= m`` and ``0 <= j <= n``:\n\n    >>> i, j = 0, 1\n    >>> V[:, (deg[1]+1)*i + j] == x**i * y**j\n    array([ True,  True])\n\n    The (1D) Vandermonde matrix of sample points ``x`` and degree ``m`` is a\n    special case of the (2D) pseudo-Vandermonde matrix with ``y`` points all\n    zero and degree ``[m, 0]``.\n\n    >>> P.polyvander2d(x=x, y=0*x, deg=(m, 0)) == P.polyvander(x=x, deg=m)\n    array([[ True,  True],\n           [ True,  True]])",
}
-/

/-  Pseudo-Vandermonde matrix of given degrees for 2D polynomials.
    Returns a matrix where V[k, (yDeg + 1)*i + j] = x[k]^i * y[k]^j
    for 0 <= i <= xDeg and 0 <= j <= yDeg. -/

/-  Specification: polyvander2d creates a pseudo-Vandermonde matrix where each entry
    satisfies the polynomial power relationship V[k, (yDeg + 1)*i + j] = x[k]^i * y[k]^j.
    The matrix has dimensions n × ((xDeg + 1) * (yDeg + 1)) and represents all polynomial
    terms x^i * y^j for 0 ≤ i ≤ xDeg and 0 ≤ j ≤ yDeg. -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def polyvander2d {n : Nat} (x y : Vector Float n) (xDeg yDeg : Nat) : 
    Id (Vector (Vector Float ((xDeg + 1) * (yDeg + 1))) n) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem polyvander2d_spec {n : Nat} (x y : Vector Float n) (xDeg yDeg : Nat) :
    ⦃⌜True⌝⦄
    polyvander2d x y xDeg yDeg
    ⦃⇓V => ⌜∀ k : Fin n, ∀ i : Fin (xDeg + 1), ∀ j : Fin (yDeg + 1),
            let colIdx := (yDeg + 1) * i.val + j.val
            let colIdxFin : Fin ((xDeg + 1) * (yDeg + 1)) := 
              ⟨colIdx, by sorry⟩
            (V.get k).get colIdxFin = (x.get k) ^ (Float.ofNat i.val) * (y.get k) ^ (Float.ofNat j.val)⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
