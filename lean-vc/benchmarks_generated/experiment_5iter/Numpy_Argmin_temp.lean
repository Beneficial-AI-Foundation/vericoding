import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def argmin_helper (a : Vector Float (n + 1)) (current_min_idx : Fin (n + 1)) (current_idx : Nat) : Fin (n + 1) :=
  if h : current_idx < n + 1 then
    let idx := ⟨current_idx, h⟩
    if a.get idx < a.get current_min_idx then
      argmin_helper a idx (current_idx + 1)
    else
      argmin_helper a current_min_idx (current_idx + 1)
  else
    current_min_idx

/-- numpy.argmin: Returns the index of the minimum value.

    Returns the index of the minimum value among all elements in the array.
    Requires a non-empty array since there is no minimum of an empty set.

    This function returns the position of the smallest element in the array.
-/
def numpy_argmin (a : Vector Float (n + 1)) : Id (Fin (n + 1)) :=
  pure (argmin_helper a ⟨0, Nat.zero_lt_succ n⟩ 0)

-- LLM HELPER
lemma argmin_helper_spec (a : Vector Float (n + 1)) (current_min_idx : Fin (n + 1)) (current_idx : Nat)
    (h : ∀ j : Fin (n + 1), j.val < current_idx → a.get current_min_idx ≤ a.get j) :
    ∀ j : Fin (n + 1), a.get (argmin_helper a current_min_idx current_idx) ≤ a.get j := by
  intro j
  induction current_idx using Nat.strong_induction_on generalizing current_min_idx with
  | ind k ih =>
    simp [argmin_helper]
    by_cases hk : k < n + 1
    · simp [hk]
      let idx := ⟨k, hk⟩
      by_cases hcomp : a.get idx < a.get current_min_idx
      · simp [hcomp]
        apply ih (k + 1)
        · simp
        · intro l hl
          simp at hl
          cases' Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hl) with h1 h2
          · exact h l h1
          · rw [←h2]
            exact le_of_lt hcomp
      · simp [hcomp]
        apply ih (k + 1)
        · simp
        · intro l hl
          simp at hl
          cases' Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hl) with h1 h2
          · exact h l h1
          · rw [←h2]
            exact le_of_not_gt hcomp
    · simp [hk]
      by_cases hj : j.val < k
      · exact h j hj
      · simp at hj
        have : k ≤ n := Nat.le_of_not_succ_le_iff.mpr hk
        have : j.val ≤ n := Nat.le_of_lt_succ j.isLt
        have : j.val = k := Nat.eq_of_le_of_lt_succ (le_of_not_gt hj) j.isLt
        rw [this] at hj
        exact absurd (Nat.le_refl k) hj

/-- Specification: numpy.argmin returns the index of the minimum element.

    Precondition: True (non-empty constraint is in the type)
    Postcondition: The element at the returned index is the minimum value
-/
theorem numpy_argmin_spec (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    numpy_argmin a
    ⦃⇓i => ⌜∀ j : Fin (n + 1), a.get i ≤ a.get j⌝⦄ := by
  simp [numpy_argmin]
  rw [pure_post]
  apply argmin_helper_spec
  intro j h
  exfalso
  exact Nat.not_lt_zero _ h