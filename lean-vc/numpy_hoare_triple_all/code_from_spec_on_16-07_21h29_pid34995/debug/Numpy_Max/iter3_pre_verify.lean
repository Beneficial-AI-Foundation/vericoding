import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.max: Maximum value in array.

    Returns the maximum value among all elements in the array.
    Requires a non-empty array since there is no maximum of an empty set.

    This is a reduction operation that finds the largest value in the array.
-/
def numpy_max (a : Vector Float (n + 1)) : Id Float :=
  pure (a.toList.foldl max (a.get 0))

-- LLM HELPER
lemma max_is_element (a : Vector Float (n + 1)) :
  ∃ i : Fin (n + 1), a.get i = a.toList.foldl max (a.get 0) := by
  have h : a.toList.foldl max (a.get 0) ∈ a.toList ∨ a.toList.foldl max (a.get 0) = a.get 0 := by
    exact List.foldl_max_mem_or_eq a.toList (a.get 0)
  cases h with
  | inl h_mem => 
    simp [Vector.toList] at h_mem
    exact h_mem
  | inr h_eq => 
    use 0
    exact h_eq.symm

-- LLM HELPER
lemma max_is_maximum (a : Vector Float (n + 1)) :
  ∀ i : Fin (n + 1), a.get i ≤ a.toList.foldl max (a.get 0) := by
  intro i
  have h : a.get i ∈ a.toList := by
    simp [Vector.toList]
    exact List.get_mem _ _ _
  exact List.le_foldl_max_of_mem h

/-- Specification: numpy.max returns the maximum element in the vector.

    Precondition: True (non-empty constraint is in the type)
    Postcondition: result is the maximum value and is an element of the vector
-/
theorem numpy_max_spec (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    numpy_max a
    ⦃⇓result => ⌜(∃ i : Fin (n + 1), a.get i = result) ∧
                (∀ i : Fin (n + 1), a.get i ≤ result)⌝⦄ := by
  unfold numpy_max
  apply hoare_triple_returns_pure
  exact ⟨max_is_element a, max_is_maximum a⟩