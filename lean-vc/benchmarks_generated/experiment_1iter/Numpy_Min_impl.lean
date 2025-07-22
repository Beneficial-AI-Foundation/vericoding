import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.min: Minimum value in array.

    Returns the minimum value among all elements in the array.
    Requires a non-empty array since there is no minimum of an empty set.

    This is a reduction operation that finds the smallest value in the array.
-/
def numpy_min (a : Vector Float (n + 1)) : Id Float :=
  pure (a.toList.minimum?.getD (a.get 0))

-- LLM HELPER
lemma vector_nonempty_minimum_exists (a : Vector Float (n + 1)) :
    ∃ x ∈ a.toList, a.toList.minimum? = some x := by
  have h : a.toList.length = n + 1 := by simp [Vector.toList_length]
  have h_nonempty : a.toList ≠ [] := by
    intro h_empty
    rw [List.length_eq_zero] at h_empty
    rw [h_empty] at h
    simp at h
  exact List.minimum?_eq_some_iff.mpr ⟨h_nonempty, rfl⟩

-- LLM HELPER
lemma vector_minimum_is_element (a : Vector Float (n + 1)) :
    ∃ i : Fin (n + 1), a.get i = a.toList.minimum?.getD (a.get 0) := by
  cases h : a.toList.minimum? with
  | none => 
    use 0
    simp [Option.getD, h]
  | some x =>
    have ⟨_, h_mem⟩ := vector_nonempty_minimum_exists a
    rw [h] at h_mem
    simp at h_mem
    have h_in_list : x ∈ a.toList := h_mem
    rw [Vector.mem_toList_iff] at h_in_list
    obtain ⟨i, hi⟩ := h_in_list
    use i
    rw [hi, Option.getD, h]

-- LLM HELPER
lemma vector_minimum_is_minimum (a : Vector Float (n + 1)) :
    ∀ i : Fin (n + 1), a.toList.minimum?.getD (a.get 0) ≤ a.get i := by
  intro i
  cases h : a.toList.minimum? with
  | none => 
    simp [Option.getD, h]
    exact le_refl _
  | some x =>
    have h_min := List.minimum?_le_iff.mp
    simp [Option.getD, h]
    have h_in_list : a.get i ∈ a.toList := by
      rw [Vector.mem_toList_iff]
      exact ⟨i, rfl⟩
    have h_some : a.toList.minimum? = some x := h
    have h_le := List.minimum?_le h_some h_in_list
    exact h_le

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
  apply And.intro
  · exact vector_minimum_is_element a
  · exact vector_minimum_is_minimum a