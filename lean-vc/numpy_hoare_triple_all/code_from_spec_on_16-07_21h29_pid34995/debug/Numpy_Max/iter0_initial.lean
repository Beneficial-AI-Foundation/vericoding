import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.max: Maximum value in array.

    Returns the maximum value among all elements in the array.
    Requires a non-empty array since there is no maximum of an empty set.

    This is a reduction operation that finds the largest value in the array.
-/
def numpy_max (a : Vector Float (n + 1)) : Id Float :=
  Id.pure (a.toList.maximum?.getD (a.get 0))

-- LLM HELPER
lemma vector_nonempty_has_max (a : Vector Float (n + 1)) : 
  a.toList.maximum? = some (a.toList.maximum?.getD (a.get 0)) := by
  have h : a.toList ≠ [] := by
    simp [Vector.toList]
    exact List.length_pos_iff_ne_nil.mp (Nat.succ_pos n)
  exact List.maximum?_some_iff.mpr h

-- LLM HELPER
lemma max_is_element (a : Vector Float (n + 1)) :
  ∃ i : Fin (n + 1), a.get i = a.toList.maximum?.getD (a.get 0) := by
  have h := vector_nonempty_has_max a
  rw [←h]
  have mem : a.toList.maximum?.getD (a.get 0) ∈ a.toList := by
    cases' hmax : a.toList.maximum? with max
    · simp at h
    · rw [Option.getD_some]
      exact List.maximum?_mem hmax
  simp [Vector.toList] at mem
  exact mem

-- LLM HELPER
lemma max_is_maximum (a : Vector Float (n + 1)) :
  ∀ i : Fin (n + 1), a.get i ≤ a.toList.maximum?.getD (a.get 0) := by
  intro i
  have h := vector_nonempty_has_max a
  rw [←h]
  cases' hmax : a.toList.maximum? with max
  · simp at h
  · rw [Option.getD_some]
    have mem : a.get i ∈ a.toList := by
      simp [Vector.toList]
      exact List.get_mem _ _ _
    exact List.le_maximum?_of_mem mem hmax

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
  simp [precondition_true]
  constructor
  · exact max_is_element a
  · exact max_is_maximum a