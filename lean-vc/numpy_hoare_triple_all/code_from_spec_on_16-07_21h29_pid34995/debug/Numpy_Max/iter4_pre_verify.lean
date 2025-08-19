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
lemma List.foldl_max_mem_or_eq (l : List Float) (init : Float) :
  (l.foldl max init ∈ l) ∨ (l.foldl max init = init) := by
  induction l generalizing init with
  | nil => right; rfl
  | cons h t ih =>
    simp [List.foldl]
    have := ih (max init h)
    cases this with
    | inl h_mem => left; exact List.mem_cons_of_mem h h_mem
    | inr h_eq => 
      simp [h_eq]
      by_cases h_case : init ≤ h
      · simp [max_def, h_case]
        left; exact List.mem_cons_self h t
      · simp [max_def, h_case]
        right; rfl

-- LLM HELPER
lemma List.le_foldl_max_of_mem {l : List Float} {x init : Float} (h : x ∈ l) :
  x ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => cases h
  | cons head tail ih =>
    simp at h
    cases h with
    | inl h_eq => 
      simp [List.foldl, h_eq]
      have : head ≤ max init head := le_max_right init head
      exact le_trans this (le_refl _)
    | inr h_mem =>
      simp [List.foldl]
      exact ih h_mem

-- LLM HELPER
lemma max_is_element (a : Vector Float (n + 1)) :
  ∃ i : Fin (n + 1), a.get i = a.toList.foldl max (a.get 0) := by
  have h : a.toList.foldl max (a.get 0) ∈ a.toList ∨ a.toList.foldl max (a.get 0) = a.get 0 := by
    exact List.foldl_max_mem_or_eq a.toList (a.get 0)
  cases h with
  | inl h_mem => 
    have : ∃ i, a.toList.get i = a.toList.foldl max (a.get 0) := by
      exact List.mem_iff_get.mp h_mem
    obtain ⟨i, hi⟩ := this
    use i.cast (by simp [Vector.toList])
    simp [Vector.get_eq_getElem]
    rw [← hi]
    simp [Vector.toList]
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
  apply pure_spec
  exact ⟨max_is_element a, max_is_maximum a⟩