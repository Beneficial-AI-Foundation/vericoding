import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.polynomial.hermite.hermmulx",
  "category": "Hermite polynomials",
  "description": "Multiply a Hermite series by x.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.hermite.hermmulx.html",
  "doc": "Multiply a Hermite series by x.\n\n    Multiply the Hermite series \`c\` by x, where x is the independent\n    variable.\n\n\n    Parameters\n    ----------\n    c : array_like\n        1-D array of Hermite series coefficients ordered from low to\n        high.\n\n    Returns\n    -------\n    out : ndarray\n        Array representing the result of the multiplication.\n\n    See Also\n    --------\n    hermadd, hermsub, hermmul, hermdiv, hermpow\n\n    Notes\n    -----\n    The multiplication uses the recursion relationship for Hermite\n    polynomials in the form\n\n    .. math::\n\n        xP_i(x) = (P_{i + 1}(x)/2 + i*P_{i - 1}(x))\n\n    Examples\n    --------\n    >>> from numpy.polynomial.hermite import hermmulx\n    >>> hermmulx([1, 2, 3])\n    array([2. , 6.5, 1. , 1.5])",
  "code": "def hermmulx(c):\n    \"\"\"Multiply a Hermite series by x.\n\n    Multiply the Hermite series \`c\` by x, where x is the independent\n    variable.\n\n\n    Parameters\n    ----------\n    c : array_like\n        1-D array of Hermite series coefficients ordered from low to\n        high.\n\n    Returns\n    -------\n    out : ndarray\n        Array representing the result of the multiplication.\n\n    See Also\n    --------\n    hermadd, hermsub, hermmul, hermdiv, hermpow\n\n    Notes\n    -----\n    The multiplication uses the recursion relationship for Hermite\n    polynomials in the form\n\n    .. math::\n\n        xP_i(x) = (P_{i + 1}(x)/2 + i*P_{i - 1}(x))\n\n    Examples\n    --------\n    >>> from numpy.polynomial.hermite import hermmulx\n    >>> hermmulx([1, 2, 3])\n    array([2. , 6.5, 1. , 1.5])\n\n    \"\"\"\n    # c is a trimmed copy\n    [c] = pu.as_series([c])\n    # The zero series needs special treatment\n    if len(c) == 1 and c[0] == 0:\n        return c\n\n    prd = np.empty(len(c) + 1, dtype=c.dtype)\n    prd[0] = c[0] * 0\n    prd[1] = c[0] / 2\n    for i in range(1, len(c)):\n        prd[i + 1] = c[i] / 2\n        prd[i - 1] += c[i] * i\n    return prd"
}
-/

open Std.Do

/-- Multiply a Hermite series by x using the recursion relationship xP_i(x) = (P_{i+1}(x)/2 + i*P_{i-1}(x)) -/
def hermmulx {n : Nat} (c : Vector Float n) : Id (Vector Float (n + 1)) :=
  sorry

/-- Specification: hermmulx multiplies a Hermite series by x using the recursion relationship for Hermite polynomials.

    The algorithm implements the recursion: $$xP_i(x) = (P_{i+1}(x)/2 + i*P_{i-1}(x))$$

    Given input coefficients c[0], c[1], ..., c[n-1], the output has n+1 coefficients where:
    - The first coefficient is always 0
    - Each c[i] contributes c[i]/2 to position i+1 and c[i]*i to position i-1

    For example, with input [1, 2, 3]:
    - result[0] = 0 + 2*1 = 2
    - result[1] = 1/2 + 3*2 = 0.5 + 6 = 6.5
    - result[2] = 2/2 = 1
    - result[3] = 3/2 = 1.5
    Giving [2, 6.5, 1, 1.5] -/
theorem hermmulx_spec {n : Nat} (c : Vector Float n) :
    ⦃⌜True⌝⦄
    hermmulx c
    ⦃⇓result =>
      -- The output has exactly n+1 coefficients
      ⌜result.size = n + 1⌝ ∧
      -- Mathematical property: each position in result is the sum of contributions
      -- from the recursion formula $xP_i(x) = (P_{i+1}(x)/2 + i*P_{i-1}(x))$
      ⌜∀ k : Fin (n + 1),
        result.get k =
          -- Base case: position 0 starts at 0
          (if k.val = 0 then 0 else 0) +
          -- Contribution from c[k-1]/2 when k > 0 and k-1 < n
          (if h1 : k.val > 0 ∧ k.val - 1 < n then c.get ⟨k.val - 1, sorry⟩ / 2 else 0) +
          -- Contribution from c[k+1]*(k+1) when k+1 < n
          (if h2 : k.val + 1 < n then c.get ⟨k.val + 1, sorry⟩ * Float.ofNat (k.val + 1) else 0)⌝
    ⦄ := by
  sorry
