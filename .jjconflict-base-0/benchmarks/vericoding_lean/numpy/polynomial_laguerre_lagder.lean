import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.polynomial.laguerre.lagder",
  "category": "Laguerre polynomials",
  "description": "Differentiate a Laguerre series.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.laguerre.lagder.html",
  "doc": "Differentiate a Laguerre series.\n\n    Returns the Laguerre series coefficients \`c\` differentiated \`m\` times\n    along \`axis\`.  At each iteration the result is multiplied by \`scl\` (the\n    scaling factor is for use in a linear change of variable). The argument\n    \`c\` is an array of coefficients from low to high degree along each\n    axis, e.g., [1,2,3] represents the series \`\`1*L_0 + 2*L_1 + 3*L_2\`\`\n    while [[1,2],[1,2]] represents \`\`1*L_0(x)*L_0(y) + 1*L_1(x)*L_0(y) +\n    2*L_0(x)*L_1(y) + 2*L_1(x)*L_1(y)\`\` if axis=0 is \`\`x\`\` and axis=1 is\n    \`\`y\`\`.\n\n    Parameters\n    ----------\n    c : array_like\n        Array of Laguerre series coefficients. If \`c\` is multidimensional\n        the different axis correspond to different variables with the\n        degree in each axis given by the corresponding index.\n    m : int, optional\n        Number of derivatives taken, must be non-negative. (Default: 1)\n    scl : scalar, optional\n        Each differentiation is multiplied by \`scl\`.  The end result is\n        multiplication by \`\`scl**m\`\`.  This is for use in a linear change of\n        variable. (Default: 1)\n    axis : int, optional\n        Axis over which the derivative is taken. (Default: 0).\n\n    Returns\n    -------\n    der : ndarray\n        Laguerre series of the derivative.\n\n    See Also\n    --------\n    lagint\n\n    Notes\n    -----\n    In general, the result of differentiating a Laguerre series does not\n    resemble the same operation on a power series. Thus the result of this\n    function may be \"unintuitive,\" albeit correct; see Examples section\n    below.\n\n    Examples\n    --------\n    >>> from numpy.polynomial.laguerre import lagder\n    >>> lagder([ 1.,  1.,  1., -3.])\n    array([1.,  2.,  3.])\n    >>> lagder([ 1.,  0.,  0., -4.,  3.], m=2)\n    array([1.,  2.,  3.])",
  "code": "def lagder(c, m=1, scl=1, axis=0):\n    \"\"\"\n    Differentiate a Laguerre series.\n\n    Returns the Laguerre series coefficients \`c\` differentiated \`m\` times\n    along \`axis\`.  At each iteration the result is multiplied by \`scl\` (the\n    scaling factor is for use in a linear change of variable). The argument\n    \`c\` is an array of coefficients from low to high degree along each\n    axis, e.g., [1,2,3] represents the series \`\`1*L_0 + 2*L_1 + 3*L_2\`\`\n    while [[1,2],[1,2]] represents \`\`1*L_0(x)*L_0(y) + 1*L_1(x)*L_0(y) +\n    2*L_0(x)*L_1(y) + 2*L_1(x)*L_1(y)\`\` if axis=0 is \`\`x\`\` and axis=1 is\n    \`\`y\`\`.\n\n    Parameters\n    ----------\n    c : array_like\n        Array of Laguerre series coefficients. If \`c\` is multidimensional\n        the different axis correspond to different variables with the\n        degree in each axis given by the corresponding index.\n    m : int, optional\n        Number of derivatives taken, must be non-negative. (Default: 1)\n    scl : scalar, optional\n        Each differentiation is multiplied by \`scl\`.  The end result is\n        multiplication by \`\`scl**m\`\`.  This is for use in a linear change of\n        variable. (Default: 1)\n    axis : int, optional\n        Axis over which the derivative is taken. (Default: 0).\n\n    Returns\n    -------\n    der : ndarray\n        Laguerre series of the derivative.\n\n    See Also\n    --------\n    lagint\n\n    Notes\n    -----\n    In general, the result of differentiating a Laguerre series does not\n    resemble the same operation on a power series. Thus the result of this\n    function may be \"unintuitive,\" albeit correct; see Examples section\n    below.\n\n    Examples\n    --------\n    >>> from numpy.polynomial.laguerre import lagder\n    >>> lagder([ 1.,  1.,  1., -3.])\n    array([1.,  2.,  3.])\n    >>> lagder([ 1.,  0.,  0., -4.,  3.], m=2)\n    array([1.,  2.,  3.])\n\n    \"\"\"\n    c = np.array(c, ndmin=1, copy=True)\n    if c.dtype.char in '?bBhHiIlLqQpP':\n        c = c.astype(np.double)\n\n    cnt = pu._as_int(m, \"the order of derivation\")\n    iaxis = pu._as_int(axis, \"the axis\")\n    if cnt < 0:\n        raise ValueError(\"The order of derivation must be non-negative\")\n    iaxis = normalize_axis_index(iaxis, c.ndim)\n\n    if cnt == 0:\n        return c\n\n    c = np.moveaxis(c, iaxis, 0)\n    n = len(c)\n    if cnt >= n:\n        c = c[:1] * 0\n    else:\n        for i in range(cnt):\n            n = n - 1\n            c *= scl\n            der = np.empty((n,) + c.shape[1:], dtype=c.dtype)\n            for j in range(n, 1, -1):\n                der[j - 1] = -c[j]\n                c[j - 1] += c[j]\n            der[0] = -c[1]\n            c = der\n    c = np.moveaxis(c, 0, iaxis)\n    return c"
}
-/

/-- Differentiates a Laguerre series m times with optional scaling.
    Returns the coefficients of the differentiated Laguerre series. -/
def lagder {n : Nat} (c : Vector Float n) (m : Nat) (scl : Float := 1.0) : 
    Id (Vector Float n) :=
  sorry

/-- Specification: lagder differentiates a Laguerre series m times.
    Each differentiation is scaled by scl and follows Laguerre polynomial recurrence relations. -/
theorem lagder_spec {n : Nat} (c : Vector Float n) (m : Nat) (scl : Float) :
    ⦃⌜True⌝⦄
    lagder c m scl
    ⦃⇓result => ⌜-- Basic properties
                 result.size = n ∧
                 -- If m = 0, result equals input
                 (m = 0 → ∀ i : Fin n, result.get i = c.get i) ∧
                 -- For large m, result becomes zero or minimal
                 (m ≥ n ∧ n > 0 → ∀ i : Fin n, result.get i = 0)⌝⦄ := by
  sorry