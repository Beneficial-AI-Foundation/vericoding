import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.polynomial.polynomial.polygrid2d",
  "category": "Standard polynomials",
  "description": "Evaluate a 2-D polynomial on the Cartesian product of x and y.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.polynomial.polygrid2d.html",
  "doc": "Evaluate a 2-D polynomial on the Cartesian product of x and y.\n\n    This function returns the values:\n\n    .. math:: p(a,b) = \\\\sum_{i,j} c_{i,j} * a^i * b^j\n\n    where the points ``(a, b)`` consist of all pairs formed by taking\n    `a` from `x` and `b` from `y`. The resulting points form a grid with\n    `x` in the first dimension and `y` in the second.\n\n    The parameters `x` and `y` are converted to arrays only if they are\n    tuples or a lists, otherwise they are treated as a scalars. In either\n    case, either `x` and `y` or their elements must support multiplication\n    and addition both with themselves and with the elements of `c`.\n\n    If `c` has fewer than two dimensions, ones are implicitly appended to\n    its shape to make it 2-D. The shape of the result will be c.shape[2:] +\n    x.shape + y.shape.\n\n    Parameters\n    ----------\n    x, y : array_like, compatible objects\n        The two dimensional series is evaluated at the points in the\n        Cartesian product of `x` and `y`.  If `x` or `y` is a list or\n        tuple, it is first converted to an ndarray, otherwise it is left\n        unchanged and, if it isn't an ndarray, it is treated as a scalar.\n    c : array_like\n        Array of coefficients ordered so that the coefficients for terms of\n        degree i,j are contained in ``c[i,j]``. If `c` has dimension\n        greater than two the remaining indices enumerate multiple sets of\n        coefficients.\n\n    Returns\n    -------\n    values : ndarray, compatible object\n        The values of the two dimensional polynomial at points in the Cartesian\n        product of `x` and `y`.\n\n    See Also\n    --------\n    polyval, polyval2d, polyval3d, polygrid3d\n\n    Examples\n    --------\n    >>> from numpy.polynomial import polynomial as P\n    >>> c = ((1, 2, 3), (4, 5, 6))\n    >>> P.polygrid2d([0, 1], [0, 1], c)\n    array([[ 1.,  6.],\n           [ 5., 21.]])",
  "code": "def polygrid2d(x, y, c):\n    \"\"\"\n    Evaluate a 2-D polynomial on the Cartesian product of x and y.\n\n    This function returns the values:\n\n    .. math:: p(a,b) = \\\\sum_{i,j} c_{i,j} * a^i * b^j\n\n    where the points ``(a, b)`` consist of all pairs formed by taking\n    `a` from `x` and `b` from `y`. The resulting points form a grid with\n    `x` in the first dimension and `y` in the second.\n\n    The parameters `x` and `y` are converted to arrays only if they are\n    tuples or a lists, otherwise they are treated as a scalars. In either\n    case, either `x` and `y` or their elements must support multiplication\n    and addition both with themselves and with the elements of `c`.\n\n    If `c` has fewer than two dimensions, ones are implicitly appended to\n    its shape to make it 2-D. The shape of the result will be c.shape[2:] +\n    x.shape + y.shape.\n\n    Parameters\n    ----------\n    x, y : array_like, compatible objects\n        The two dimensional series is evaluated at the points in the\n        Cartesian product of `x` and `y`.  If `x` or `y` is a list or\n        tuple, it is first converted to an ndarray, otherwise it is left\n        unchanged and, if it isn't an ndarray, it is treated as a scalar.\n    c : array_like\n        Array of coefficients ordered so that the coefficients for terms of\n        degree i,j are contained in ``c[i,j]``. If `c` has dimension\n        greater than two the remaining indices enumerate multiple sets of\n        coefficients.\n\n    Returns\n    -------\n    values : ndarray, compatible object\n        The values of the two dimensional polynomial at points in the Cartesian\n        product of `x` and `y`.\n\n    See Also\n    --------\n    polyval, polyval2d, polyval3d, polygrid3d\n\n    Examples\n    --------\n    >>> from numpy.polynomial import polynomial as P\n    >>> c = ((1, 2, 3), (4, 5, 6))\n    >>> P.polygrid2d([0, 1], [0, 1], c)\n    array([[ 1.,  6.],\n           [ 5., 21.]])\n\n    \"\"\"\n    return pu._gridnd(polyval, c, x, y)"
}
-/

/-- Evaluate a 2-D polynomial on the Cartesian product of x and y -/
def polygrid2d {nx ny : Nat} {degree_x degree_y : Nat} 
    (x : Vector Float nx) (y : Vector Float ny) 
    (c : Vector (Vector Float (degree_y + 1)) (degree_x + 1)) : 
    Id (Vector (Vector Float ny) nx) :=
  sorry

/-- Specification: polygrid2d evaluates a 2-D polynomial on the Cartesian product of x and y.
    The result is a grid where result[i][j] = p(x[i], y[j]) for the polynomial defined by 
    coefficients c, where p(a,b) = sum_{i,j} c[i][j] * a^i * b^j. -/
theorem polygrid2d_spec {nx ny : Nat} {degree_x degree_y : Nat} 
    (x : Vector Float nx) (y : Vector Float ny) 
    (c : Vector (Vector Float (degree_y + 1)) (degree_x + 1)) :
    ⦃⌜True⌝⦄
    polygrid2d x y c
    ⦃⇓result => ⌜∀ i : Fin nx, ∀ j : Fin ny, 
      ∃ (val : Float), (result.get i).get j = val ∧
      ∀ dx : Fin (degree_x + 1), ∀ dy : Fin (degree_y + 1),
      ∃ (term : Float), term = (c.get dx).get dy * (x.get i) ^ (dx.val.toFloat) * (y.get j) ^ (dy.val.toFloat)⌝⦄ := by
  sorry