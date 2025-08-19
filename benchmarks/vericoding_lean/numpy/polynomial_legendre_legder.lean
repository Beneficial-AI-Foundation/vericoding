import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.polynomial.legendre.legder",
  "category": "Legendre polynomials",
  "description": "Differentiate a Legendre series.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.legendre.legder.html",
  "doc": "Differentiate a Legendre series.\n\n    Returns the Legendre series coefficients \`c\` differentiated \`m\` times\n    along \`axis\`.  At each iteration the result is multiplied by \`scl\` (the\n    scaling factor is for use in a linear change of variable). The argument\n    \`c\` is an array of coefficients from low to high degree along each\n    axis, e.g., [1,2,3] represents the series \`\`1*L_0 + 2*L_1 + 3*L_2\`\`\n    while [[1,2],[1,2]] represents \`\`1*L_0(x)*L_0(y) + 1*L_1(x)*L_0(y) +\n    2*L_0(x)*L_1(y) + 2*L_1(x)*L_1(y)\`\` if axis=0 is \`\`x\`\` and axis=1 is\n    \`\`y\`\`.\n\n    Parameters\n    ----------\n    c : array_like\n        Array of Legendre series coefficients. If c is multidimensional the\n        different axis correspond to different variables with the degree in\n        each axis given by the corresponding index.\n    m : int, optional\n        Number of derivatives taken, must be non-negative. (Default: 1)\n    scl : scalar, optional\n        Each differentiation is multiplied by \`scl\`.  The end result is\n        multiplication by \`\`scl**m\`\`.  This is for use in a linear change of\n        variable. (Default: 1)\n    axis : int, optional\n        Axis over which the derivative is taken. (Default: 0).\n\n    Returns\n    -------\n    der : ndarray\n        Legendre series of the derivative.\n\n    See Also\n    --------\n    legint\n\n    Notes\n    -----\n    In general, the result of differentiating a Legendre series does not\n    resemble the same operation on a power series. Thus the result of this\n    function may be \"unintuitive,\" albeit correct; see Examples section\n    below.\n\n    Examples\n    --------\n    >>> from numpy.polynomial import legendre as L\n    >>> c = (1,2,3,4)\n    >>> L.legder(c)\n    array([  6.,   9.,  20.])\n    >>> L.legder(c, 3)\n    array([60.])\n    >>> L.legder(c, scl=-1)\n    array([ -6.,  -9., -20.])\n    >>> L.legder(c, 2,-1)\n    array([  9.,  60.])",
  "code": "def legder(c, m=1, scl=1, axis=0):\n    \"\"\"\n    Differentiate a Legendre series.\n\n    Returns the Legendre series coefficients \`c\` differentiated \`m\` times\n    along \`axis\`.  At each iteration the result is multiplied by \`scl\` (the\n    scaling factor is for use in a linear change of variable). The argument\n    \`c\` is an array of coefficients from low to high degree along each\n    axis, e.g., [1,2,3] represents the series \`\`1*L_0 + 2*L_1 + 3*L_2\`\`\n    while [[1,2],[1,2]] represents \`\`1*L_0(x)*L_0(y) + 1*L_1(x)*L_0(y) +\n    2*L_0(x)*L_1(y) + 2*L_1(x)*L_1(y)\`\` if axis=0 is \`\`x\`\` and axis=1 is\n    \`\`y\`\`.\n\n    Parameters\n    ----------\n    c : array_like\n        Array of Legendre series coefficients. If c is multidimensional the\n        different axis correspond to different variables with the degree in\n        each axis given by the corresponding index.\n    m : int, optional\n        Number of derivatives taken, must be non-negative. (Default: 1)\n    scl : scalar, optional\n        Each differentiation is multiplied by \`scl\`.  The end result is\n        multiplication by \`\`scl**m\`\`.  This is for use in a linear change of\n        variable. (Default: 1)\n    axis : int, optional\n        Axis over which the derivative is taken. (Default: 0).\n\n    Returns\n    -------\n    der : ndarray\n        Legendre series of the derivative.\n\n    See Also\n    --------\n    legint\n\n    Notes\n    -----\n    In general, the result of differentiating a Legendre series does not\n    resemble the same operation on a power series. Thus the result of this\n    function may be \"unintuitive,\" albeit correct; see Examples section\n    below.\n\n    Examples\n    --------\n    >>> from numpy.polynomial import legendre as L\n    >>> c = (1,2,3,4)\n    >>> L.legder(c)\n    array([  6.,   9.,  20.])\n    >>> L.legder(c, 3)\n    array([60.])\n    >>> L.legder(c, scl=-1)\n    array([ -6.,  -9., -20.])\n    >>> L.legder(c, 2,-1)\n    array([  9.,  60.])\n\n    \"\"\"\n    c = np.array(c, ndmin=1, copy=True)\n    if c.dtype.char in '?bBhHiIlLqQpP':\n        c = c.astype(np.double)\n    cnt = pu._as_int(m, \"the order of derivation\")\n    iaxis = pu._as_int(axis, \"the axis\")\n    if cnt < 0:\n        raise ValueError(\"The order of derivation must be non-negative\")\n    iaxis = normalize_axis_index(iaxis, c.ndim)\n\n    if cnt == 0:\n        return c\n\n    c = np.moveaxis(c, iaxis, 0)\n    n = len(c)\n    if cnt >= n:\n        c = c[:1] * 0\n    else:\n        for i in range(cnt):\n            n = n - 1\n            c *= scl\n            der = np.empty((n,) + c.shape[1:], dtype=c.dtype)\n            for j in range(n, 2, -1):\n                der[j - 1] = (2 * j - 1) * c[j]\n                c[j - 2] += c[j]\n            if n > 1:\n                der[1] = 3 * c[2]\n            der[0] = c[1]\n            c = der\n    c = np.moveaxis(c, 0, iaxis)\n    return c"
}
-/

/-- Differentiate a Legendre series.
    Returns the Legendre series coefficients c differentiated m times.
    Each differentiation is multiplied by scl (scaling factor). -/
def legder {n : Nat} (c : Vector Float n) (m : Nat) (scl : Float) : Id (Vector Float (max 1 (n - m))) :=
  sorry

/-- Specification: legder computes the derivative of a Legendre series -/
theorem legder_spec {n : Nat} (c : Vector Float n) (m : Nat) (scl : Float) (h : n ≥ 1) :
    ⦃⌜n ≥ 1⌝⦄
    legder c m scl
    ⦃⇓result => ⌜
      -- Result size is correct
      (result.size = max 1 (n - m)) ∧
      -- If m = 0, result equals input (identity operation)
      (m = 0 → result.size = n ∧ ∀ i : Fin n, ∃ j : Fin result.size, result.get j = c.get i) ∧
      -- If m >= n, result is zero vector of length 1
      (m ≥ n → result.size = 1)
    ⌝⦄ := by
  sorry
