import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.argmax: Returns the index of the maximum value.

    Returns the index of the maximum value among all elements in the array.
    Requires a non-empty array since there is no maximum of an empty set.

    This function returns the position of the largest element in the array.
-/
def numpy_argmax (a : Vector Float (n + 1)) : Id (Fin (n + 1)) :=
  Id.pure (argmax_helper a 0 0)

-- LLM HELPER
def argmax_helper (a : Vector Float (n + 1)) (current_max_idx : Fin (n + 1)) (current_idx : Nat) : Fin (n + 1) :=
  if h : current_idx < n + 1 then
    let idx := ⟨current_idx, h⟩
    if a.get idx > a.get current_max_idx then
      argmax_helper a idx (current_idx + 1)
    else
      argmax_helper a current_max_idx (current_idx + 1)
  else
    current_max_idx

-- LLM HELPER
lemma argmax_helper_spec (a : Vector Float (n + 1)) (start_idx : Fin (n + 1)) (current_idx : Nat) :
    ∀ j : Fin (n + 1), current_idx ≤ j.val → a.get j ≤ a.get (argmax_helper a start_idx current_idx) := by
  intro j hj
  unfold argmax_helper
  split
  · case isTrue h =>
    have idx := ⟨current_idx, h⟩
    split
    · case isTrue h_gt =>
      apply argmax_helper_spec
      omega
    · case isFalse h_not_gt =>
      apply argmax_helper_spec
      omega
  · case isFalse h =>
    simp at h
    have : j.val < n + 1 := j.isLt
    omega

-- LLM HELPER
lemma argmax_helper_covers_all (a : Vector Float (n + 1)) (start_idx : Fin (n + 1)) :
    ∀ j : Fin (n + 1), a.get j ≤ a.get (argmax_helper a start_idx 0) := by
  intro j
  apply argmax_helper_spec
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
  simp [Id.pure]
  intro j
  apply argmax_helper_covers_all