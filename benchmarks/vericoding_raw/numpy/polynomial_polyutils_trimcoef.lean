import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.polynomial.polyutils.trimcoef",
  "category": "Polynomial utilities",
  "description": "Remove \"small\" \"trailing\" coefficients from a polynomial.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.polyutils.trimcoef.html",
  "doc": "Remove \"small\" \"trailing\" coefficients from a polynomial.\n\n    \"Small\" means \"small in absolute value\" and is controlled by the\n    parameter \`tol\`; \"trailing\" means highest order coefficient(s), e.g., in\n    \`\`[0, 1, 1, 0, 0]\`\` (which represents \`\`0 + x + x**2 + 0*x**3 + 0*x**4\`\`)\n    both the 3-rd and 4-th order coefficients would be \"trimmed.\"\n\n    Parameters\n    ----------\n    c : array_like\n        1-d array of coefficients, ordered from lowest order to highest.\n    tol : number, optional\n        Trailing (i.e., highest order) elements with absolute value less\n        than or equal to \`tol\` (default value is zero) are removed.\n\n    Returns\n    -------\n    trimmed : ndarray\n        1-d array with trailing zeros removed.  If the resulting series\n        would be empty, a series containing a single zero is returned.\n\n    Raises\n    ------\n    ValueError\n        If \`tol\` < 0\n\n    Examples\n    --------\n    >>> from numpy.polynomial import polyutils as pu\n    >>> pu.trimcoef((0,0,3,0,5,0,0))\n    array([0.,  0.,  3.,  0.,  5.])\n    >>> pu.trimcoef((0,0,1e-3,0,1e-5,0,0),1e-3) # item == tol is trimmed\n    array([0.])\n    >>> i = complex(0,1) # works for complex\n    >>> pu.trimcoef((3e-4,1e-3*(1-i),5e-4,2e-5*(1+i)), 1e-3)\n    array([0.0003+0.j   , 0.001 -0.001j])",
  "code": "def trimcoef(c, tol=0):\n    \"\"\"\n    Remove \"small\" \"trailing\" coefficients from a polynomial.\n\n    \"Small\" means \"small in absolute value\" and is controlled by the\n    parameter \`tol\`; \"trailing\" means highest order coefficient(s), e.g., in\n    \`\`[0, 1, 1, 0, 0]\`\` (which represents \`\`0 + x + x**2 + 0*x**3 + 0*x**4\`\`)\n    both the 3-rd and 4-th order coefficients would be \"trimmed.\"\n\n    Parameters\n    ----------\n    c : array_like\n        1-d array of coefficients, ordered from lowest order to highest.\n    tol : number, optional\n        Trailing (i.e., highest order) elements with absolute value less\n        than or equal to \`tol\` (default value is zero) are removed.\n\n    Returns\n    -------\n    trimmed : ndarray\n        1-d array with trailing zeros removed.  If the resulting series\n        would be empty, a series containing a single zero is returned.\n\n    Raises\n    ------\n    ValueError\n        If \`tol\` < 0\n\n    Examples\n    --------\n    >>> from numpy.polynomial import polyutils as pu\n    >>> pu.trimcoef((0,0,3,0,5,0,0))\n    array([0.,  0.,  3.,  0.,  5.])\n    >>> pu.trimcoef((0,0,1e-3,0,1e-5,0,0),1e-3) # item == tol is trimmed\n    array([0.])\n    >>> i = complex(0,1) # works for complex\n    >>> pu.trimcoef((3e-4,1e-3*(1-i),5e-4,2e-5*(1+i)), 1e-3)\n    array([0.0003+0.j   , 0.001 -0.001j])\n\n    \"\"\"\n    if tol < 0:\n        raise ValueError(\"tol must be non-negative\")\n\n    [c] = as_series([c])\n    [ind] = np.nonzero(np.abs(c) > tol)\n    if len(ind) == 0:\n        return c[:1] * 0\n    else:\n        return c[:ind[-1] + 1].copy()"
}
-/

open Std.Do

/-- Remove "small" "trailing" coefficients from a polynomial.
    Small means small in absolute value controlled by tolerance parameter.
    Trailing means highest order coefficients. -/
def trimcoef {n : Nat} (c : Vector Float n) (tol : Float) : Id (Vector Float (n + 1)) :=
  sorry

/-- Specification: trimcoef removes trailing coefficients with absolute value ≤ tol.
    If all coefficients are small, returns a single zero.
    The tolerance must be non-negative. -/
theorem trimcoef_spec {n : Nat} (c : Vector Float n) (tol : Float) 
    (h_tol_nonneg : tol ≥ 0) :
    ⦃⌜tol ≥ 0⌝⦄
    trimcoef c tol
    ⦃⇓result => ⌜
      -- Basic sanity: result is non-empty
      (∃ m : Nat, m ≥ 1) ∧
      -- Special case: if all input coefficients are small, return single zero
      ((∀ i : Fin n, Float.abs (c.get i) ≤ tol) → 
        (∃ h : 0 < n + 1, result.get ⟨0, h⟩ = 0)) ∧
      -- General case: preserve coefficients up to the last significant one
      ((∃ i : Fin n, Float.abs (c.get i) > tol) → 
        (∃ last_significant : Fin n, 
          -- last_significant is the rightmost index with coefficient > tol
          (Float.abs (c.get last_significant) > tol) ∧
          (∀ j : Fin n, j > last_significant → Float.abs (c.get j) ≤ tol) ∧
          -- All coefficients up to last_significant are preserved in order
          (∀ i : Fin n, i.val ≤ last_significant.val → 
            (∃ h : i.val < n + 1, result.get ⟨i.val, h⟩ = c.get i)))) ∧
      -- Mathematical correctness: no large coefficients are lost
      (∀ i : Fin n, Float.abs (c.get i) > tol → 
        (∃ j : Fin (n + 1), result.get j = c.get i)) ∧
      -- Trimming guarantee: result has no trailing large coefficients
      (∀ i : Fin (n + 1), (∀ j : Fin (n + 1), j > i → Float.abs (result.get j) ≤ tol) →
        (∀ k : Fin (n + 1), k ≥ i → Float.abs (result.get k) ≤ tol))
    ⌝⦄ := by
  sorry