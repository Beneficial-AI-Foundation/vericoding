import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def Vector.maxIndexAux (a : Vector Float (n + 1)) (i : Fin (n + 1)) (maxIdx : Fin (n + 1)) : Fin (n + 1) :=
  if h : i.val < n then
    let nextIdx : Fin (n + 1) := ⟨i.val + 1, Nat.succ_lt_succ_iff.mpr h⟩
    if a.get nextIdx > a.get maxIdx then
      Vector.maxIndexAux a nextIdx nextIdx
    else
      Vector.maxIndexAux a nextIdx maxIdx
  else
    maxIdx

-- LLM HELPER
def Vector.maxIndex (a : Vector Float (n + 1)) : Fin (n + 1) :=
  Vector.maxIndexAux a ⟨0, Nat.zero_lt_succ n⟩ ⟨0, Nat.zero_lt_succ n⟩

-- LLM HELPER
lemma Vector.maxIndexAux_spec (a : Vector Float (n + 1)) (i : Fin (n + 1)) (maxIdx : Fin (n + 1)) 
    (h : ∀ j : Fin (n + 1), j.val < i.val → a.get j ≤ a.get maxIdx) :
    ∀ j : Fin (n + 1), j.val ≤ i.val → a.get j ≤ a.get (Vector.maxIndexAux a i maxIdx) := by
  intro j hj
  induction' n using Nat.strong_induction_on with n ih generalizing i maxIdx j
  simp [Vector.maxIndexAux]
  split
  · next h_lt =>
    have nextIdx : Fin (n + 1) := ⟨i.val + 1, Nat.succ_lt_succ_iff.mpr h_lt⟩
    split
    · next h_gt =>
      apply ih
      · exact Nat.lt_succ_self n
      · intro k hk
        by_cases hk_eq : k.val = nextIdx.val
        · simp [hk_eq]
          exact le_of_lt h_gt
        · have hk_lt : k.val < i.val := by
            have : k.val < nextIdx.val := by
              cases' Nat.lt_or_eq_of_le (Nat.le_of_succ_le_succ hk) with h_lt h_eq
              · exact h_lt
              · contradiction
            exact Nat.lt_of_succ_le this
          exact h k hk_lt
      · cases' Nat.lt_or_eq_of_le hj with h_lt h_eq
        · exact Nat.le_succ_of_le (Nat.le_of_lt h_lt)
        · simp [h_eq]
          exact Nat.succ_le_succ (Nat.le_refl _)
    · next h_le =>
      apply ih
      · exact Nat.lt_succ_self n
      · intro k hk
        by_cases hk_eq : k.val = nextIdx.val
        · simp [hk_eq]
          exact h_le
        · have hk_lt : k.val < i.val := by
            have : k.val < nextIdx.val := by
              cases' Nat.lt_or_eq_of_le (Nat.le_of_succ_le_succ hk) with h_lt h_eq
              · exact h_lt
              · contradiction
            exact Nat.lt_of_succ_le this
          exact h k hk_lt
      · cases' Nat.lt_or_eq_of_le hj with h_lt h_eq
        · exact Nat.le_succ_of_le (Nat.le_of_lt h_lt)
        · simp [h_eq]
          exact Nat.succ_le_succ (Nat.le_refl _)
  · next h_ge =>
    have : i.val = n := Nat.eq_of_le_of_lt_succ (Nat.le_of_not_gt h_ge) i.isLt
    have : j.val ≤ n := Nat.le_trans hj (this ▸ Nat.le_refl _)
    by_cases hj_lt : j.val < i.val
    · exact h j hj_lt
    · have : j.val = i.val := Nat.eq_of_le_of_not_gt (Nat.le_of_not_gt hj_lt) (this ▸ Nat.not_lt_of_le hj)
      simp [this]
      exact h maxIdx (this ▸ Nat.lt_irrefl _)

-- LLM HELPER
lemma Vector.maxIndex_spec (a : Vector Float (n + 1)) :
    ∀ j : Fin (n + 1), a.get j ≤ a.get (Vector.maxIndex a) := by
  intro j
  simp [Vector.maxIndex]
  apply Vector.maxIndexAux_spec
  · intro k hk
    exfalso
    exact Nat.not_lt_zero _ hk
  · exact Nat.zero_le _

/-- numpy.argmax: Returns the index of the maximum value.

    Returns the index of the maximum value among all elements in the array.
    Requires a non-empty array since there is no maximum of an empty set.

    This function returns the position of the largest element in the array.
-/
def numpy_argmax (a : Vector Float (n + 1)) : Id (Fin (n + 1)) :=
  pure (Vector.maxIndex a)

/-- Specification: numpy.argmax returns the index of the maximum element.

    Precondition: True (non-empty constraint is in the type)
    Postcondition: The element at the returned index is the maximum value
-/
theorem numpy_argmax_spec (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    numpy_argmax a
    ⦃⇓i => ⌜∀ j : Fin (n + 1), a.get j ≤ a.get i⌝⦄ := by
  simp [numpy_argmax]
  apply pure_spec
  exact Vector.maxIndex_spec a