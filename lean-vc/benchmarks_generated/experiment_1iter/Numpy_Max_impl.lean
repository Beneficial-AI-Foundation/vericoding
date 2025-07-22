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
lemma max_in_foldl (l : List Float) (init : Float) (h : init ∈ init :: l) :
  ∃ x ∈ init :: l, List.foldl max init l = x := by
  induction l generalizing init with
  | nil => 
    simp [List.foldl]
    exact ⟨init, List.mem_cons_self _ _, rfl⟩
  | cons head tail ih =>
    simp [List.foldl]
    have : max init head ∈ init :: head :: tail := by
      cases' le_total init head with h h
      · simp [max_def, h]
        exact List.mem_cons_of_mem _ (List.mem_cons_self _ _)
      · simp [max_def, h]
        exact List.mem_cons_self _ _
    exact ih this

-- LLM HELPER
lemma foldl_max_ge (l : List Float) (init : Float) (x : Float) (h : x ∈ init :: l) :
  x ≤ List.foldl max init l := by
  induction l generalizing init with
  | nil => 
    simp [List.foldl] at h
    rw [h]
  | cons head tail ih =>
    simp [List.foldl]
    cases' h with h h
    · rw [h]
      exact le_max_left _ _
    · cases' h with h h
      · rw [h]
        exact le_max_right _ _
      · exact ih (List.mem_cons_of_mem _ h)

/-- Specification: numpy.max returns the maximum element in the vector.

    Precondition: True (non-empty constraint is in the type)
    Postcondition: result is the maximum value and is an element of the vector
-/
theorem numpy_max_spec (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    numpy_max a
    ⦃⇓result => ⌜(∃ i : Fin (n + 1), a.get i = result) ∧
                (∀ i : Fin (n + 1), a.get i ≤ result)⌝⦄ := by
  simp [numpy_max, spec_pure]
  constructor
  · have h := max_in_foldl a.toList (a.get 0) (by simp [Vector.toList_get])
    obtain ⟨x, hx_mem, hx_eq⟩ := h
    simp [Vector.toList_get] at hx_mem
    cases' hx_mem with hx_mem hx_mem
    · rw [← hx_mem] at hx_eq
      exact ⟨0, hx_eq⟩
    · obtain ⟨i, hi, hx_mem⟩ := hx_mem
      rw [← hx_mem] at hx_eq
      exact ⟨i.succ, hx_eq⟩
  · intro i
    have h : a.get i ∈ a.get 0 :: a.toList := by
      cases' i with i hi
      · exact List.mem_cons_self _ _
      · simp [Vector.toList_get]
        exact ⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, rfl, rfl⟩
    exact foldl_max_ge a.toList (a.get 0) (a.get i) h