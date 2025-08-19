import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.polynomial.hermite_e.hermeder",
  "category": "HermiteE polynomials",
  "description": "Differentiate a Hermite_e series.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.hermite_e.hermeder.html",
  "doc": "Differentiate a Hermite_e series.\n\n    Returns the series coefficients \`c\` differentiated \`m\` times along\n    \`axis\`.  At each iteration the result is multiplied by \`scl\` (the\n    scaling factor is for use in a linear change of variable). The argument\n    \`c\` is an array of coefficients from low to high degree along each\n    axis, e.g., [1,2,3] represents the series \`\`1*He_0 + 2*He_1 + 3*He_2\`\`\n    while [[1,2],[1,2]] represents \`\`1*He_0(x)*He_0(y) + 1*He_1(x)*He_0(y)\n    + 2*He_0(x)*He_1(y) + 2*He_1(x)*He_1(y)\`\` if axis=0 is \`\`x\`\` and axis=1\n    is \`\`y\`\`.\n\n    Parameters\n    ----------\n    c : array_like\n        Array of Hermite_e series coefficients. If \`c\` is multidimensional\n        the different axis correspond to different variables with the\n        degree in each axis given by the corresponding index.\n    m : int, optional\n        Number of derivatives taken, must be non-negative. (Default: 1)\n    scl : scalar, optional\n        Each differentiation is multiplied by \`scl\`.  The end result is\n        multiplication by \`\`scl**m\`\`.  This is for use in a linear change of\n        variable. (Default: 1)\n    axis : int, optional\n        Axis over which the derivative is taken. (Default: 0).\n\n    Returns\n    -------\n    der : ndarray\n        Hermite series of the derivative.\n\n    See Also\n    --------\n    hermeint\n\n    Notes\n    -----\n    In general, the result of differentiating a Hermite series does not\n    resemble the same operation on a power series. Thus the result of this\n    function may be \"unintuitive,\" albeit correct; see Examples section\n    below.\n\n    Examples\n    --------\n    >>> from numpy.polynomial.hermite_e import hermeder\n    >>> hermeder([ 1.,  1.,  1.,  1.])\n    array([1.,  2.,  3.])\n    >>> hermeder([-0.25,  1.,  1./2.,  1./3.,  1./4 ], m=2)\n    array([1.,  2.,  3.])",
  "code": "def hermeder(c, m=1, scl=1, axis=0):\n    \"\"\"\n    Differentiate a Hermite_e series.\n\n    Returns the series coefficients \`c\` differentiated \`m\` times along\n    \`axis\`.  At each iteration the result is multiplied by \`scl\` (the\n    scaling factor is for use in a linear change of variable). The argument\n    \`c\` is an array of coefficients from low to high degree along each\n    axis, e.g., [1,2,3] represents the series \`\`1*He_0 + 2*He_1 + 3*He_2\`\`\n    while [[1,2],[1,2]] represents \`\`1*He_0(x)*He_0(y) + 1*He_1(x)*He_0(y)\n    + 2*He_0(x)*He_1(y) + 2*He_1(x)*He_1(y)\`\` if axis=0 is \`\`x\`\` and axis=1\n    is \`\`y\`\`.\n\n    Parameters\n    ----------\n    c : array_like\n        Array of Hermite_e series coefficients. If \`c\` is multidimensional\n        the different axis correspond to different variables with the\n        degree in each axis given by the corresponding index.\n    m : int, optional\n        Number of derivatives taken, must be non-negative. (Default: 1)\n    scl : scalar, optional\n        Each differentiation is multiplied by \`scl\`.  The end result is\n        multiplication by \`\`scl**m\`\`.  This is for use in a linear change of\n        variable. (Default: 1)\n    axis : int, optional\n        Axis over which the derivative is taken. (Default: 0).\n\n    Returns\n    -------\n    der : ndarray\n        Hermite series of the derivative.\n\n    See Also\n    --------\n    hermeint\n\n    Notes\n    -----\n    In general, the result of differentiating a Hermite series does not\n    resemble the same operation on a power series. Thus the result of this\n    function may be \"unintuitive,\" albeit correct; see Examples section\n    below.\n\n    Examples\n    --------\n    >>> from numpy.polynomial.hermite_e import hermeder\n    >>> hermeder([ 1.,  1.,  1.,  1.])\n    array([1.,  2.,  3.])\n    >>> hermeder([-0.25,  1.,  1./2.,  1./3.,  1./4 ], m=2)\n    array([1.,  2.,  3.])\n\n    \"\"\"\n    c = np.array(c, ndmin=1, copy=True)\n    if c.dtype.char in '?bBhHiIlLqQpP':\n        c = c.astype(np.double)\n    cnt = pu._as_int(m, \"the order of derivation\")\n    iaxis = pu._as_int(axis, \"the axis\")\n    if cnt < 0:\n        raise ValueError(\"The order of derivation must be non-negative\")\n    iaxis = normalize_axis_index(iaxis, c.ndim)\n\n    if cnt == 0:\n        return c\n\n    c = np.moveaxis(c, iaxis, 0)\n    n = len(c)\n    if cnt >= n:\n        return c[:1] * 0\n    else:\n        for i in range(cnt):\n            n = n - 1\n            c *= scl\n            der = np.empty((n,) + c.shape[1:], dtype=c.dtype)\n            for j in range(n, 0, -1):\n                der[j - 1] = j * c[j]\n            c = der\n    c = np.moveaxis(c, 0, iaxis)\n    return c"
}
-/

open Std.Do

/-- Differentiate a Hermite_e series by taking the derivative of coefficients.
    Takes coefficients from low to high degree and returns differentiated coefficients. -/
def hermeder {n : Nat} (c : Vector Float (n + 1)) (m : Nat) (scl : Float) : Id (Vector Float n) :=
  sorry

/-- Specification: hermeder correctly differentiates Hermite_e series coefficients.
    The result has degree reduced by 1, and each coefficient is multiplied by its index
    and scaled by scl^m. For a single differentiation (m=1), the coefficient of degree k
    becomes k * scl * original_coefficient. -/
theorem hermeder_spec {n : Nat} (c : Vector Float (n + 1)) (m : Nat) (scl : Float) 
    (h_pos_scl : scl > 0) (h_pos_m : m > 0) :
    ⦃⌜scl > 0 ∧ m > 0⌝⦄
    hermeder c m scl
    ⦃⇓result => ⌜
      -- For single differentiation (m=1), each coefficient follows the derivative rule
      (m = 1 → ∀ i : Fin n, result.get i = (i.val.toFloat + 1.0) * scl * c.get ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) ∧
      -- For multiple differentiation, the scaling factor is applied m times
      (∀ i : Fin n, Float.abs (result.get i) ≤ Float.abs scl * (n.toFloat + 1.0) * 10.0) ∧
      -- If all input coefficients are zero, result is zero
      (∀ i : Fin (n + 1), c.get i = 0 → ∀ j : Fin n, result.get j = 0)
    ⌝⦄ := by
  sorry