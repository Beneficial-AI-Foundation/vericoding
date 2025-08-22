import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.polynomial.polynomial.polygrid3d",
  "category": "Standard polynomials",
  "description": "Evaluate a 3-D polynomial on the Cartesian product of x, y and z.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.polynomial.polygrid3d.html",
  "doc": "Evaluate a 3-D polynomial on the Cartesian product of x, y and z.\n\n    This function returns the values:\n\n    .. math:: p(a,b,c) = \\\\sum_{i,j,k} c_{i,j,k} * a^i * b^j * c^k\n\n    where the points ``(a, b, c)`` consist of all triples formed by taking\n    `a` from `x`, `b` from `y`, and `c` from `z`. The resulting points form\n    a grid with `x` in the first dimension, `y` in the second, and `z` in\n    the third.\n\n    The parameters `x`, `y`, and `z` are converted to arrays only if they\n    are tuples or a lists, otherwise they are treated as a scalars. In\n    either case, either `x`, `y`, and `z` or their elements must support\n    multiplication and addition both with themselves and with the elements\n    of `c`.\n\n    If `c` has fewer than three dimensions, ones are implicitly appended to\n    its shape to make it 3-D. The shape of the result will be c.shape[3:] +\n    x.shape + y.shape + z.shape.\n\n    Parameters\n    ----------\n    x, y, z : array_like, compatible objects\n        The three dimensional series is evaluated at the points in the\n        Cartesian product of `x`, `y`, and `z`.  If `x`, `y`, or `z` is a\n        list or tuple, it is first converted to an ndarray, otherwise it is\n        left unchanged and, if it isn't an ndarray, it is treated as a\n        scalar.\n    c : array_like\n        Array of coefficients ordered so that the coefficients for terms of\n        degree i,j are contained in ``c[i,j]``. If `c` has dimension\n        greater than two the remaining indices enumerate multiple sets of\n        coefficients.\n\n    Returns\n    -------\n    values : ndarray, compatible object\n        The values of the two dimensional polynomial at points in the Cartesian\n        product of `x` and `y`.\n\n    See Also\n    --------\n    polyval, polyval2d, polygrid2d, polyval3d\n\n    Examples\n    --------\n    >>> from numpy.polynomial import polynomial as P\n    >>> c = ((1, 2, 3), (4, 5, 6), (7, 8, 9))\n    >>> P.polygrid3d([0, 1], [0, 1], [0, 1], c)\n    array([[ 1., 13.],\n           [ 6., 51.]])",
  "code": "def polygrid3d(x, y, z, c):\n    \"\"\"\n    Evaluate a 3-D polynomial on the Cartesian product of x, y and z.\n\n    This function returns the values:\n\n    .. math:: p(a,b,c) = \\\\sum_{i,j,k} c_{i,j,k} * a^i * b^j * c^k\n\n    where the points ``(a, b, c)`` consist of all triples formed by taking\n    `a` from `x`, `b` from `y`, and `c` from `z`. The resulting points form\n    a grid with `x` in the first dimension, `y` in the second, and `z` in\n    the third.\n\n    The parameters `x`, `y`, and `z` are converted to arrays only if they\n    are tuples or a lists, otherwise they are treated as a scalars. In\n    either case, either `x`, `y`, and `z` or their elements must support\n    multiplication and addition both with themselves and with the elements\n    of `c`.\n\n    If `c` has fewer than three dimensions, ones are implicitly appended to\n    its shape to make it 3-D. The shape of the result will be c.shape[3:] +\n    x.shape + y.shape + z.shape.\n\n    Parameters\n    ----------\n    x, y, z : array_like, compatible objects\n        The three dimensional series is evaluated at the points in the\n        Cartesian product of `x`, `y`, and `z`.  If `x`, `y`, or `z` is a\n        list or tuple, it is first converted to an ndarray, otherwise it is\n        left unchanged and, if it isn't an ndarray, it is treated as a\n        scalar.\n    c : array_like\n        Array of coefficients ordered so that the coefficients for terms of\n        degree i,j are contained in ``c[i,j]``. If `c` has dimension\n        greater than two the remaining indices enumerate multiple sets of\n        coefficients.\n\n    Returns\n    -------\n    values : ndarray, compatible object\n        The values of the two dimensional polynomial at points in the Cartesian\n        product of `x` and `y`.\n\n    See Also\n    --------\n    polyval, polyval2d, polygrid2d, polyval3d\n\n    Examples\n    --------\n    >>> from numpy.polynomial import polynomial as P\n    >>> c = ((1, 2, 3), (4, 5, 6), (7, 8, 9))\n    >>> P.polygrid3d([0, 1], [0, 1], [0, 1], c)\n    array([[ 1., 13.],\n           [ 6., 51.]])\n\n    \"\"\"\n    return pu._gridnd(polyval, c, x, y, z)"
}
-/

/-- Evaluate a 3-D polynomial on the Cartesian product of x, y and z -/
def polygrid3d {nx ny nz : Nat} {degree_x degree_y degree_z : Nat} 
    (x : Vector Float nx) (y : Vector Float ny) (z : Vector Float nz)
    (c : Vector (Vector (Vector Float (degree_z + 1)) (degree_y + 1)) (degree_x + 1)) : 
    Id (Vector (Vector (Vector Float nz) ny) nx) :=
  sorry

/-- Specification: polygrid3d evaluates a 3-D polynomial on the Cartesian product of x, y and z.
    The result is a 3D grid where result[i][j][k] = p(x[i], y[j], z[k]) for the polynomial 
    defined by coefficients c, where p(a,b,c) = sum_{i,j,k} c[i][j][k] * a^i * b^j * c^k. -/
theorem polygrid3d_spec {nx ny nz : Nat} {degree_x degree_y degree_z : Nat} 
    (x : Vector Float nx) (y : Vector Float ny) (z : Vector Float nz)
    (c : Vector (Vector (Vector Float (degree_z + 1)) (degree_y + 1)) (degree_x + 1)) :
    ⦃⌜True⌝⦄
    polygrid3d x y z c
    ⦃⇓result => ⌜∀ i : Fin nx, ∀ j : Fin ny, ∀ k : Fin nz,
      ∃ (val : Float), ((result.get i).get j).get k = val ∧
      ∀ dx : Fin (degree_x + 1), ∀ dy : Fin (degree_y + 1), ∀ dz : Fin (degree_z + 1),
      ∃ (term : Float), term = ((c.get dx).get dy).get dz * (x.get i) ^ (dx.val.toFloat) * (y.get j) ^ (dy.val.toFloat) * (z.get k) ^ (dz.val.toFloat)⌝⦄ := by
  sorry