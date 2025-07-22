import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def find_max_index_aux (a : Vector Float (n + 1)) (i : Fin (n + 1)) (current_max_idx : Fin (n + 1)) : Fin (n + 1) :=
  if h : i.val < n + 1 then
    if i.val + 1 < n + 1 then
      let next_i := ⟨i.val + 1, by 
        have : i.val < n + 1 := h
        have : i.val + 1 ≤ n + 1 := Nat.succ_le_succ (Nat.le_of_lt_succ h)
        exact Nat.lt_of_le_of_lt this (Nat.lt_succ_self n)⟩
      if a.get i > a.get current_max_idx then
        find_max_index_aux a next_i i
      else
        find_max_index_aux a next_i current_max_idx
    else
      if a.get i > a.get current_max_idx then
        i
      else
        current_max_idx
  else
    current_max_idx

-- LLM HELPER
def find_max_index (a : Vector Float (n + 1)) : Fin (n + 1) :=
  let start_idx : Fin (n + 1) := ⟨0, Nat.succ_pos n⟩
  find_max_index_aux a start_idx start_idx

/-- numpy.argmax: Returns the index of the maximum value.

    Returns the index of the maximum value among all elements in the array.
    Requires a non-empty array since there is no maximum of an empty set.

    This function returns the position of the largest element in the array.
-/
def numpy_argmax (a : Vector Float (n + 1)) : Id (Fin (n + 1)) :=
  pure (find_max_index a)

-- LLM HELPER
lemma find_max_index_aux_correct (a : Vector Float (n + 1)) (i : Fin (n + 1)) (current_max_idx : Fin (n + 1)) :
    (∀ k : Fin (n + 1), k.val < i.val → a.get k ≤ a.get current_max_idx) →
    (∀ j : Fin (n + 1), a.get j ≤ a.get (find_max_index_aux a i current_max_idx)) := by
  intro h
  unfold find_max_index_aux
  split_ifs with h1 h2 h3 h4
  · -- Case: i.val < n + 1 and i.val + 1 < n + 1 and a.get i > a.get current_max_idx
    have : (⟨i.val + 1, by have : i.val < n + 1 := h1; have : i.val + 1 ≤ n + 1 := Nat.succ_le_succ (Nat.le_of_lt_succ h1); exact Nat.lt_of_le_of_lt this (Nat.lt_succ_self n)⟩ : Fin (n + 1)).val = i.val + 1 := rfl
    apply find_max_index_aux_correct
    intro k hk
    cases' Nat.lt_or_eq_of_le (Nat.le_of_succ_le_succ hk) with h_lt h_eq
    · exact h k h_lt
    · rw [← h_eq]; exact le_of_lt h3
  · -- Case: i.val < n + 1 and i.val + 1 < n + 1 and ¬(a.get i > a.get current_max_idx)
    apply find_max_index_aux_correct
    intro k hk
    cases' Nat.lt_or_eq_of_le (Nat.le_of_succ_le_succ hk) with h_lt h_eq
    · exact h k h_lt
    · rw [← h_eq]; exact le_of_not_gt h3
  · -- Case: i.val < n + 1 and ¬(i.val + 1 < n + 1) and a.get i > a.get current_max_idx
    intro j
    have : i.val + 1 ≥ n + 1 := Nat.le_of_not_gt h2
    have : i.val = n := by
      have : i.val < n + 1 := h1
      have : i.val + 1 ≥ n + 1 := Nat.le_of_not_gt h2
      omega
    cases' Nat.lt_or_eq_of_le (Nat.le_of_lt_succ j.isLt) with h_lt h_eq
    · exact h j h_lt
    · rw [← h_eq, this]; exact le_of_lt h3
  · -- Case: i.val < n + 1 and ¬(i.val + 1 < n + 1) and ¬(a.get i > a.get current_max_idx)
    intro j
    have : i.val + 1 ≥ n + 1 := Nat.le_of_not_gt h2
    have : i.val = n := by
      have : i.val < n + 1 := h1
      have : i.val + 1 ≥ n + 1 := Nat.le_of_not_gt h2
      omega
    cases' Nat.lt_or_eq_of_le (Nat.le_of_lt_succ j.isLt) with h_lt h_eq
    · exact h j h_lt
    · rw [← h_eq, this]; exact le_of_not_gt h3
  · -- Case: ¬(i.val < n + 1)
    intro j
    have : i.val ≥ n + 1 := Nat.le_of_not_gt h1
    have : i.val < n + 1 := i.isLt
    omega

-- LLM HELPER
lemma find_max_index_correct (a : Vector Float (n + 1)) :
    ∀ j : Fin (n + 1), a.get j ≤ a.get (find_max_index a) := by
  unfold find_max_index
  let start_idx : Fin (n + 1) := ⟨0, Nat.succ_pos n⟩
  apply find_max_index_aux_correct
  intro k hk
  have : k.val < 0 := hk
  have : k.val ≥ 0 := Nat.zero_le k.val
  omega

/-- Specification: numpy.argmax returns the index of the maximum element.

    Precondition: True (non-empty constraint is in the type)
    Postcondition: The element at the returned index is the maximum value
-/
theorem numpy_argmax_spec (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    numpy_argmax a
    ⦃⇓i => ⌜∀ j : Fin (n + 1), a.get j ≤ a.get i⌝⦄ := by
  unfold numpy_argmax
  simp
  exact find_max_index_correct a