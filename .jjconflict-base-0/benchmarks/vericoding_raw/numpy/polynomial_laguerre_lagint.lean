import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.polynomial.laguerre.lagint",
  "category": "Laguerre polynomials",
  "description": "Integrate a Laguerre series.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.laguerre.lagint.html",
  "doc": "Integrate a Laguerre series.\n\n    Returns the Laguerre series coefficients \`c\` integrated \`m\` times from\n    \`lbnd\` along \`axis\`. At each iteration the resulting series is\n    **multiplied** by \`scl\` and an integration constant, \`k\`, is added.\n    The scaling factor is for use in a linear change of variable.  (\"Buyer\n    beware\": note that, depending on what one is doing, one may want \`scl\`\n    to be the reciprocal of what one might expect; for more information,\n    see the Notes section below.)  The argument \`c\` is an array of\n    coefficients from low to high degree along each axis, e.g., [1,2,3]\n    represents the series \`\`L_0 + 2*L_1 + 3*L_2\`\` while [[1,2],[1,2]]\n    represents \`\`1*L_0(x)*L_0(y) + 1*L_1(x)*L_0(y) + 2*L_0(x)*L_1(y) +\n    2*L_1(x)*L_1(y)\`\` if axis=0 is \`\`x\`\` and axis=1 is \`\`y\`\`.\n\n\n    Parameters\n    ----------\n    c : array_like\n        Array of Laguerre series coefficients. If \`c\` is multidimensional\n        the different axis correspond to different variables with the\n        degree in each axis given by the corresponding index.\n    m : int, optional\n        Order of integration, must be positive. (Default: 1)\n    k : {[], list, scalar}, optional\n        Integration constant(s).  The value of the first integral at\n        \`\`lbnd\`\` is the first value in the list, the value of the second\n        integral at \`\`lbnd\`\` is the second value, etc.  If \`\`k == []\`\` (the\n        default), all constants are set to zero.  If \`\`m == 1\`\`, a single\n        scalar can be given instead of a list.\n    lbnd : scalar, optional\n        The lower bound of the integral. (Default: 0)\n    scl : scalar, optional\n        Following each integration the result is *multiplied* by \`scl\`\n        before the integration constant is added. (Default: 1)\n    axis : int, optional\n        Axis over which the integral is taken. (Default: 0).\n\n    Returns\n    -------\n    S : ndarray\n        Laguerre series coefficients of the integral.\n\n    Raises\n    ------\n    ValueError\n        If \`\`m < 0\`\`, \`\`len(k) > m\`\`, \`\`np.ndim(lbnd) != 0\`\`, or\n        \`\`np.ndim(scl) != 0\`\`.\n\n    See Also\n    --------\n    lagder\n\n    Notes\n    -----\n    Note that the result of each integration is *multiplied* by \`scl\`.\n    Why is this important to note?  Say one is making a linear change of\n    variable :math:\`u = ax + b\` in an integral relative to \`x\`.  Then\n    :math:\`dx = du/a\`, so one will need to set \`scl\` equal to\n    :math:\`1/a\` - perhaps not what one would have first thought.\n\n    Also note that, in general, the result of integrating a C-series needs\n    to be \"reprojected\" onto the C-series basis set.  Thus, typically,\n    the result of this function is \"unintuitive,\" albeit correct; see\n    Examples section below.\n\n    Examples\n    --------\n    >>> from numpy.polynomial.laguerre import lagint\n    >>> lagint([1,2,3])\n    array([ 1.,  1.,  1., -3.])\n    >>> lagint([1,2,3], m=2)\n    array([ 1.,  0.,  0., -4.,  3.])\n    >>> lagint([1,2,3], k=1)\n    array([ 2.,  1.,  1., -3.])\n    >>> lagint([1,2,3], lbnd=-1)\n    array([11.5,  1. ,  1. , -3. ])\n    >>> lagint([1,2], m=2, k=[1,2], lbnd=-1)\n    array([ 11.16666667,  -5.        ,  -3.        ,   2.        ]) # may vary",
  "code": "def lagint(c, m=1, k=[], lbnd=0, scl=1, axis=0):\n    \"\"\"\n    Integrate a Laguerre series.\n\n    Returns the Laguerre series coefficients \`c\` integrated \`m\` times from\n    \`lbnd\` along \`axis\`. At each iteration the resulting series is\n    **multiplied** by \`scl\` and an integration constant, \`k\`, is added.\n    The scaling factor is for use in a linear change of variable.  (\"Buyer\n    beware\": note that, depending on what one is doing, one may want \`scl\`\n    to be the reciprocal of what one might expect; for more information,\n    see the Notes section below.)  The argument \`c\` is an array of\n    coefficients from low to high degree along each axis, e.g., [1,2,3]\n    represents the series \`\`L_0 + 2*L_1 + 3*L_2\`\` while [[1,2],[1,2]]\n    represents \`\`1*L_0(x)*L_0(y) + 1*L_1(x)*L_0(y) + 2*L_0(x)*L_1(y) +\n    2*L_1(x)*L_1(y)\`\` if axis=0 is \`\`x\`\` and axis=1 is \`\`y\`\`.\n\n\n    Parameters\n    ----------\n    c : array_like\n        Array of Laguerre series coefficients. If \`c\` is multidimensional\n        the different axis correspond to different variables with the\n        degree in each axis given by the corresponding index.\n    m : int, optional\n        Order of integration, must be positive. (Default: 1)\n    k : {[], list, scalar}, optional\n        Integration constant(s).  The value of the first integral at\n        \`\`lbnd\`\` is the first value in the list, the value of the second\n        integral at \`\`lbnd\`\` is the second value, etc.  If \`\`k == []\`\` (the\n        default), all constants are set to zero.  If \`\`m == 1\`\`, a single\n        scalar can be given instead of a list.\n    lbnd : scalar, optional\n        The lower bound of the integral. (Default: 0)\n    scl : scalar, optional\n        Following each integration the result is *multiplied* by \`scl\`\n        before the integration constant is added. (Default: 1)\n    axis : int, optional\n        Axis over which the integral is taken. (Default: 0).\n\n    Returns\n    -------\n    S : ndarray\n        Laguerre series coefficients of the integral.\n\n    Raises\n    ------\n    ValueError\n        If \`\`m < 0\`\`, \`\`len(k) > m\`\`, \`\`np.ndim(lbnd) != 0\`\`, or\n        \`\`np.ndim(scl) != 0\`\`.\n\n    See Also\n    --------\n    lagder\n\n    Notes\n    -----\n    Note that the result of each integration is *multiplied* by \`scl\`.\n    Why is this important to note?  Say one is making a linear change of\n    variable :math:\`u = ax + b\` in an integral relative to \`x\`.  Then\n    :math:\`dx = du/a\`, so one will need to set \`scl\` equal to\n    :math:\`1/a\` - perhaps not what one would have first thought.\n\n    Also note that, in general, the result of integrating a C-series needs\n    to be \"reprojected\" onto the C-series basis set.  Thus, typically,\n    the result of this function is \"unintuitive,\" albeit correct; see\n    Examples section below.\n\n    Examples\n    --------\n    >>> from numpy.polynomial.laguerre import lagint\n    >>> lagint([1,2,3])\n    array([ 1.,  1.,  1., -3.])\n    >>> lagint([1,2,3], m=2)\n    array([ 1.,  0.,  0., -4.,  3.])\n    >>> lagint([1,2,3], k=1)\n    array([ 2.,  1.,  1., -3.])\n    >>> lagint([1,2,3], lbnd=-1)\n    array([11.5,  1. ,  1. , -3. ])\n    >>> lagint([1,2], m=2, k=[1,2], lbnd=-1)\n    array([ 11.16666667,  -5.        ,  -3.        ,   2.        ]) # may vary\n\n    \"\"\"\n    c = np.array(c, ndmin=1, copy=True)\n    if c.dtype.char in '?bBhHiIlLqQpP':\n        c = c.astype(np.double)\n    if not np.iterable(k):\n        k = [k]\n    cnt = pu._as_int(m, \"the order of integration\")\n    iaxis = pu._as_int(axis, \"the axis\")\n    if cnt < 0:\n        raise ValueError(\"The order of integration must be non-negative\")\n    if len(k) > cnt:\n        raise ValueError(\"Too many integration constants\")\n    if np.ndim(lbnd) != 0:\n        raise ValueError(\"lbnd must be a scalar.\")\n    if np.ndim(scl) != 0:\n        raise ValueError(\"scl must be a scalar.\")\n    iaxis = normalize_axis_index(iaxis, c.ndim)\n\n    if cnt == 0:\n        return c\n\n    c = np.moveaxis(c, iaxis, 0)\n    k = list(k) + [0] * (cnt - len(k))\n    for i in range(cnt):\n        n = len(c)\n        c *= scl\n        if n == 1 and np.all(c[0] == 0):\n            c[0] += k[i]\n        else:\n            tmp = np.empty((n + 1,) + c.shape[1:], dtype=c.dtype)\n            tmp[0] = c[0]\n            tmp[1] = -c[0]\n            for j in range(1, n):\n                tmp[j] += c[j]\n                tmp[j + 1] = -c[j]\n            tmp[0] += k[i] - lagval(lbnd, tmp)\n            c = tmp\n    c = np.moveaxis(c, 0, iaxis)\n    return c"
}
-/

open Std.Do

/-- numpy.polynomial.laguerre.lagint: Integrate a Laguerre series.

    Returns the Laguerre series coefficients c integrated m times from
    lbnd. At each iteration the resulting series is multiplied by scl 
    and an integration constant k is added. The scaling factor is for use 
    in a linear change of variable.

    The argument c is a vector of coefficients from low to high degree,
    e.g., [1,2,3] represents the series L_0 + 2*L_1 + 3*L_2.
-/
def lagint {n : Nat} (c : Vector Float n) (m : Nat) (k : Vector Float m) 
    (lbnd : Float) (scl : Float) : Id (Vector Float (n + m)) :=
  sorry

/-- Specification: lagint integrates a Laguerre series.

    Returns the Laguerre series coefficients c integrated m times from lbnd.
    At each iteration the resulting series is multiplied by scl and an
    integration constant is added.

    Precondition: Integration order m must be non-negative
    Postcondition: The result represents the integrated Laguerre series
    with increased degree due to integration.

    Mathematical properties:
    1. The result has degree n + m - 1 (m integrations increase degree by m)
    2. Integration is linear: lagint(α*c1 + β*c2) = α*lagint(c1) + β*lagint(c2) 
    3. For zero coefficients, integration with constants gives the constant
    4. Multiple integrations accumulate degree increases
-/
theorem lagint_spec {n : Nat} (c : Vector Float n) (m : Nat) (k : Vector Float m) 
    (lbnd : Float) (scl : Float) :
    ⦃⌜True⌝⦄
    lagint c m k lbnd scl
    ⦃⇓result => ⌜
      -- Result has correct degree: integration increases degree
      result.size = n + m ∧
      -- Each coefficient exists 
      (∀ i : Fin (n + m), ∃ val : Float, result.get i = val) ∧
      -- Scaling property: scl affects the integration result
      (scl ≠ 0 → ∀ c' : Vector Float n,
        (∀ i : Fin n, c'.get i = scl * c.get i) →
        ∃ result' : Vector Float (n + m),
          (∀ i : Fin (n + m), ∃ scale_factor : Float, 
            result'.get i = scale_factor * result.get i)) ∧
      -- Integration constant property: constants are added to the result
      (∀ i : Fin m, ∃ influence : Float, 
        influence = k.get i)
    ⌝⦄ := by
  sorry