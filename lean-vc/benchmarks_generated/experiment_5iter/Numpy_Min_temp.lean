import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.min: Minimum value in array.

    Returns the minimum value among all elements in the array.
    Requires a non-empty array since there is no minimum of an empty set.

    This is a reduction operation that finds the smallest value in the array.
-/
def numpy_min (a : Vector Float (n + 1)) : Id Float :=
  pure (a.toList.foldl min (a.get 0))

-- LLM HELPER
lemma minimum_is_element (a : Vector Float (n + 1)) :
  ∃ i : Fin (n + 1), a.get i = a.toList.foldl min (a.get 0) := by
  have h : a.toList.foldl min (a.get 0) ∈ a.toList := by
    apply List.foldl_mem_of_mem_cons
    simp [Vector.toList]
    exact List.get_mem _ _ _
  simp [Vector.toList] at h
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp h
  use ⟨i, by simp [← a.property]; exact i.isLt⟩
  simp [Vector.get]
  exact hi.symm

-- LLM HELPER
lemma minimum_is_minimal (a : Vector Float (n + 1)) :
  ∀ i : Fin (n + 1), a.toList.foldl min (a.get 0) ≤ a.get i := by
  intro i
  have h : a.toList.foldl min (a.get 0) ≤ a.get i := by
    apply List.foldl_le_of_le_of_mem
    · exact le_refl _
    · simp [Vector.toList]
      exact List.get_mem _ _ _
  exact h

/-- Specification: numpy.min returns the minimum element in the vector.

    Precondition: True (non-empty constraint is in the type)
    Postcondition: result is the minimum value and is an element of the vector
-/
theorem numpy_min_spec (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    numpy_min a
    ⦃⇓result => ⌜(∃ i : Fin (n + 1), a.get i = result) ∧
                (∀ i : Fin (n + 1), result ≤ a.get i)⌝⦄ := by
  simp [numpy_min]
  apply Triple.pure
  exact ⟨minimum_is_element a, minimum_is_minimal a⟩