import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.polynomial.laguerre.lagmul",
  "category": "Laguerre polynomials",
  "description": "Multiply one Laguerre series by another.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.laguerre.lagmul.html",
  "doc": "Multiply one Laguerre series by another.\n\n    Returns the product of two Laguerre series \`c1\` * \`c2\`.  The arguments\n    are sequences of coefficients, from lowest order \"term\" to highest,\n    e.g., [1,2,3] represents the series \`\`P_0 + 2*P_1 + 3*P_2\`\`.\n\n    Parameters\n    ----------\n    c1, c2 : array_like\n        1-D arrays of Laguerre series coefficients ordered from low to\n        high.\n\n    Returns\n    -------\n    out : ndarray\n        Of Laguerre series coefficients representing their product.\n\n    See Also\n    --------\n    lagadd, lagsub, lagmulx, lagdiv, lagpow\n\n    Notes\n    -----\n    In general, the (polynomial) product of two C-series results in terms\n    that are not in the Laguerre polynomial basis set.  Thus, to express\n    the product as a Laguerre series, it is necessary to \"reproject\" the\n    product onto said basis set, which may produce \"unintuitive\" (but\n    correct) results; see Examples section below.\n\n    Examples\n    --------\n    >>> from numpy.polynomial.laguerre import lagmul\n    >>> lagmul([1, 2, 3], [0, 1, 2])\n    array([  8., -13.,  38., -51.,  36.])\n\n    \"\"\"\n    # s1, s2 are trimmed copies\n    [c1, c2] = pu.as_series([c1, c2])\n\n    if len(c1) > len(c2):\n        c = c2\n        xs = c1\n    else:\n        c = c1\n        xs = c2\n\n    if len(c) == 1:\n        c0 = c[0] * xs\n        c1 = 0\n    elif len(c) == 2:\n        c0 = c[0] * xs\n        c1 = c[1] * xs\n    else:\n        nd = len(c)\n        c0 = c[-2] * xs\n        c1 = c[-1] * xs\n        for i in range(3, len(c) + 1):\n            tmp = c0\n            nd = nd - 1\n            c0 = lagsub(c[-i] * xs, (c1 * (nd - 1)) / nd)\n            c1 = lagadd(tmp, lagsub((2 * nd - 1) * c1, lagmulx(c1)) / nd)\n    return lagadd(c0, lagsub(c1, lagmulx(c1)))"
}
-/

-- LLM HELPER
def vectorFromList (l : List Float) : Vector Float l.length :=
  ⟨l.toArray, by simp⟩

-- LLM HELPER
def convolution {n m : Nat} (c1 : Vector Float (n + 1)) (c2 : Vector Float (m + 1)) : Vector Float (n + m + 1) :=
  let result := List.range (n + m + 1) |>.map (fun i =>
    List.range (min (i + 1) (n + 1)) |>.map (fun j =>
      if h : j < n + 1 ∧ i - j < m + 1 then
        c1.get ⟨j, h.1⟩ * c2.get ⟨i - j, h.2⟩
      else
        0
    ) |>.sum
  )
  have h : result.length = n + m + 1 := by simp [result]
  ⟨result.toArray, by simp [h]⟩

/-- Multiply one Laguerre series by another -/
def lagmul {n m : Nat} (c1 : Vector Float (n + 1)) (c2 : Vector Float (m + 1)) : Id (Vector Float (n + m + 1)) :=
  pure (convolution c1 c2)

-- LLM HELPER
lemma wp_pure {α : Type*} (x : α) (Q : α → Prop) : 
  (⦃⌜True⌝⦄ pure x ⦃⇓y => ⌜Q y⌝⦄) ↔ Q x := by
  simp [Triple.wp_pure]

/-- Specification: lagmul returns the product of two Laguerre series in coefficient form -/
theorem lagmul_spec {n m : Nat} (c1 : Vector Float (n + 1)) (c2 : Vector Float (m + 1)) :
    ⦃⌜True⌝⦄
    lagmul c1 c2
    ⦃⇓result => ⌜result.size = n + m + 1 ∧ 
                 ∀ i : Fin (n + m + 1), result.get i ≠ 0 → 
                   ∃ (j : Fin (n + 1)) (k : Fin (m + 1)), 
                     j.val + k.val = i.val ∧ c1.get j ≠ 0 ∧ c2.get k ≠ 0⌝⦄ := by
  unfold lagmul
  rw [wp_pure]
  constructor
  · rfl
  · intro i hi
    unfold convolution at hi
    simp at hi
    have : ∃ j ∈ List.range (min (i.val + 1) (n + 1)), 
      (if h : j < n + 1 ∧ i.val - j < m + 1 then c1.get ⟨j, h.1⟩ * c2.get ⟨i.val - j, h.2⟩ else 0) ≠ 0 := by
      by_contra h
      push_neg at h
      simp at hi
      have : (List.range (min (i.val + 1) (n + 1))).map (fun j => 
        if h : j < n + 1 ∧ i.val - j < m + 1 then c1.get ⟨j, h.1⟩ * c2.get ⟨i.val - j, h.2⟩ else 0) = 
        List.replicate (min (i.val + 1) (n + 1)) 0 := by
        apply List.ext_get
        · simp
        · intro k hk
          simp
          apply h
          simp at hk
          exact hk
      rw [this] at hi
      simp at hi
    obtain ⟨j, hj_mem, hj_ne⟩ := this
    simp at hj_mem
    have hj_bounds : j < n + 1 ∧ i.val - j < m + 1 := by
      by_contra h
      push_neg at h
      simp at hj_ne
      rw [if_neg h] at hj_ne
      exact hj_ne rfl
    simp at hj_ne
    rw [if_pos hj_bounds] at hj_ne
    have h_prod : c1.get ⟨j, hj_bounds.1⟩ ≠ 0 ∧ c2.get ⟨i.val - j, hj_bounds.2⟩ ≠ 0 := by
      by_contra h
      push_neg at h
      cases h with
      | inl h => rw [h] at hj_ne; simp at hj_ne
      | inr h => rw [h] at hj_ne; simp at hj_ne
    use ⟨j, hj_bounds.1⟩, ⟨i.val - j, hj_bounds.2⟩
    simp
    constructor
    · simp [Nat.add_sub_cancel']
    · exact h_prod