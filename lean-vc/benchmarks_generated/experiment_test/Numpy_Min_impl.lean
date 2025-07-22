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
lemma vector_nonempty_has_minimum (a : Vector Float (n + 1)) : 
  a.toList.minimum? = some (a.toList.minimum?.getD (a.get 0)) := by
  have h : a.toList ≠ [] := by
    simp [Vector.toList]
    exact List.length_pos_iff_ne_nil.mp (Nat.succ_pos n)
  exact List.minimum?_eq_some_iff.mpr ⟨h, List.minimum_mem h⟩

-- LLM HELPER
lemma minimum_is_element (a : Vector Float (n + 1)) :
  ∃ i : Fin (n + 1), a.get i = a.toList.minimum?.getD (a.get 0) := by
  have h : a.toList ≠ [] := by
    simp [Vector.toList]
    exact List.length_pos_iff_ne_nil.mp (Nat.succ_pos n)
  have min_mem : a.toList.minimum?.getD (a.get 0) ∈ a.toList := by
    rw [← vector_nonempty_has_minimum]
    exact List.minimum_mem h
  have : ∃ i : Fin (n + 1), a.toList.get ⟨i.val, by simp [Vector.toList]; exact i.isLt⟩ = a.toList.minimum?.getD (a.get 0) := by
    simp [Vector.toList] at min_mem
    exact List.mem_iff_get.mp min_mem
  obtain ⟨i, hi⟩ := this
  use i
  rw [← hi]
  simp [Vector.get, Vector.toList]

-- LLM HELPER
lemma minimum_is_smallest (a : Vector Float (n + 1)) (i : Fin (n + 1)) :
  a.toList.minimum?.getD (a.get 0) ≤ a.get i := by
  have h : a.toList ≠ [] := by
    simp [Vector.toList]
    exact List.length_pos_iff_ne_nil.mp (Nat.succ_pos n)
  have : a.get i ∈ a.toList := by
    simp [Vector.toList, Vector.get]
    exact List.get_mem _ _ _
  exact List.minimum_le this

/-- Specification: numpy.min returns the minimum element in the vector.

    Precondition: True (non-empty constraint is in the type)
    Postcondition: result is the minimum value and is an element of the vector
-/
theorem numpy_min_spec (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    numpy_min a
    ⦃⇓result => ⌜(∃ i : Fin (n + 1), a.get i = result) ∧
                (∀ i : Fin (n + 1), result ≤ a.get i)⌝⦄ := by
  apply Pure.triple_pure
  constructor
  · exact minimum_is_element a
  · exact minimum_is_smallest a