import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.polynomial.hermite_e.hermemulx",
  "category": "HermiteE polynomials",
  "description": "Multiply a Hermite series by x.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.hermite_e.hermemulx.html",
  "doc": "Multiply a Hermite series by x.\n\n    Multiply the Hermite series \`c\` by x, where x is the independent\n    variable.\n\n\n    Parameters\n    ----------\n    c : array_like\n        1-D array of Hermite series coefficients ordered from low to\n        high.\n\n    Returns\n    -------\n    out : ndarray\n        Array representing the result of the multiplication.\n\n    See Also\n    --------\n    hermeadd, hermesub, hermemul, hermediv, hermepow\n\n    Notes\n    -----\n    The multiplication uses the recursion relationship for Hermite\n    polynomials in the form\n\n    .. math::\n\n        xP_i(x) = (P_{i + 1}(x) + iP_{i - 1}(x)))\n\n    Examples\n    --------\n    >>> from numpy.polynomial.hermite_e import hermemulx\n    >>> hermemulx([1, 2, 3])\n    array([2.,  7.,  2.,  3.])",
  "code": "def hermemulx(c):\n    \"\"\"Multiply a Hermite series by x.\n\n    Multiply the Hermite series \`c\` by x, where x is the independent\n    variable.\n\n\n    Parameters\n    ----------\n    c : array_like\n        1-D array of Hermite series coefficients ordered from low to\n        high.\n\n    Returns\n    -------\n    out : ndarray\n        Array representing the result of the multiplication.\n\n    See Also\n    --------\n    hermeadd, hermesub, hermemul, hermediv, hermepow\n\n    Notes\n    -----\n    The multiplication uses the recursion relationship for Hermite\n    polynomials in the form\n\n    .. math::\n\n        xP_i(x) = (P_{i + 1}(x) + iP_{i - 1}(x)))\n\n    Examples\n    --------\n    >>> from numpy.polynomial.hermite_e import hermemulx\n    >>> hermemulx([1, 2, 3])\n    array([2.,  7.,  2.,  3.])\n\n    \"\"\"\n    # c is a trimmed copy\n    [c] = pu.as_series([c])\n    # The zero series needs special treatment\n    if len(c) == 1 and c[0] == 0:\n        return c\n\n    prd = np.empty(len(c) + 1, dtype=c.dtype)\n    prd[0] = c[0] * 0\n    prd[1] = c[0]\n    for i in range(1, len(c)):\n        prd[i + 1] = c[i]\n        prd[i - 1] += c[i] * i\n    return prd"
}
-/

open Std.Do

-- LLM HELPER
def hermemulx_aux {n : Nat} (c : Vector Float n) : Vector Float (n + 1) :=
  if n = 0 then 
    Vector.cons 0 Vector.nil
  else
    let mut result := Vector.replicate (n + 1) 0
    result := result.set ⟨0, by simp⟩ 0
    if n > 0 then
      result := result.set ⟨1, by simp⟩ (c.get ⟨0, by simp_all⟩)
    for i in [1:n] do
      if i < n then
        result := result.set ⟨i + 1, by simp_all⟩ (c.get ⟨i, by simp_all⟩)
        let old_val := result.get ⟨i - 1, by simp_all⟩
        result := result.set ⟨i - 1, by simp_all⟩ (old_val + c.get ⟨i, by simp_all⟩ * i.toFloat)
    result

/-- Multiply a Hermite series by x using the recursion relationship for Hermite polynomials. -/
def hermemulx {n : Nat} (c : Vector Float n) : Id (Vector Float (n + 1)) :=
  pure (hermemulx_aux c)

/-- Specification: hermemulx multiplies a Hermite series by x using the recursion relationship.
    The result has one more coefficient than the input, implementing the transformation
    based on the Hermite polynomial recursion: xP_i(x) = (P_{i + 1}(x) + iP_{i - 1}(x)) -/
theorem hermemulx_spec {n : Nat} (c : Vector Float n) :
    ⦃⌜True⌝⦄
    hermemulx c
    ⦃⇓result => ⌜
      -- Coefficient at position 0 is always 0 (no constant term in x*polynomial)
      result.get ⟨0, by simp⟩ = 0 ∧
      -- For n > 0: coefficient at position 1 comes from c[0] plus recursive contributions  
      (∀ (h : n > 0), result.get ⟨1, by simp⟩ = c.get ⟨0, h⟩ + 
        (if n > 1 then (c.get ⟨1, by simp_all⟩) * (1 : Float) else 0)) ∧
      -- For i ≥ 1: result[i+1] gets c[i] (coefficient shift up)
      (∀ i : Fin n, i.val ≥ 1 → result.get ⟨i.val + 1, by simp_all⟩ = c.get i)
    ⌝⦄ := by
  unfold hermemulx
  simp only [pure_bind, pure_return, returnSpec]
  simp only [True_implies_iff]
  unfold hermemulx_aux
  split
  · case h_1 h =>
    simp [h]
    constructor
    · simp [Vector.cons, Vector.get]
    constructor
    · intro h_pos
      simp [h] at h_pos
    · intro i h_ge
      simp [h] at i
      exact i.elim
  · case h_2 h =>
    simp
    constructor
    · simp [Vector.get, Vector.set, Vector.replicate]
    constructor
    · intro h_pos
      simp [Vector.get, Vector.set, Vector.replicate]
      cases' n with n'
      · simp at h_pos
      · simp
    · intro i h_ge
      simp [Vector.get, Vector.set, Vector.replicate]
      cases' n with n'
      · simp at i
        exact i.elim
      · simp