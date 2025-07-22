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
lemma max_in_foldl {l : List Float} {init : Float} :
  ∃ x, (x = init ∨ x ∈ l) ∧ l.foldl max init = x := by
  induction l generalizing init with
  | nil => exact ⟨init, Or.inl rfl, rfl⟩
  | cons h t ih =>
    obtain ⟨x, hx_mem, hx_eq⟩ := ih (max init h)
    exact ⟨x, by
      cases hx_mem with
      | inl h_eq => 
        rw [h_eq]
        by_cases h_case : init ≤ h
        · simp [max_def, h_case]
          exact Or.inr (List.mem_cons_self h t)
        · simp [max_def, h_case]
          exact Or.inl rfl
      | inr h_in => exact Or.inr (List.mem_cons_of_mem h h_in), hx_eq⟩

-- LLM HELPER
lemma foldl_max_ge {l : List Float} {init : Float} {x : Float} :
  x ∈ l → x ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => simp
  | cons h t ih =>
    intro h_mem
    cases h_mem with
    | head => 
      simp [List.foldl]
      have : h ≤ max init h := le_max_right init h
      exact le_trans this (ih (List.mem_cons_self h t))
    | tail _ h_tail =>
      simp [List.foldl]
      exact ih h_tail

-- LLM HELPER
lemma foldl_max_ge_init {l : List Float} {init : Float} :
  init ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => simp [List.foldl]
  | cons h t ih =>
    simp [List.foldl]
    have : init ≤ max init h := le_max_left init h
    exact le_trans this ih

-- LLM HELPER
lemma vector_get_in_toList {a : Vector Float (n + 1)} {i : Fin (n + 1)} :
  a.get i ∈ a.toList := by
  rw [Vector.toList_get]
  exact List.get_mem a.toList i

/-- Specification: numpy.max returns the maximum element in the vector.

    Precondition: True (non-empty constraint is in the type)
    Postcondition: result is the maximum value and is an element of the vector
-/
theorem numpy_max_spec (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    numpy_max a
    ⦃⇓result => ⌜(∃ i : Fin (n + 1), a.get i = result) ∧
                (∀ i : Fin (n + 1), a.get i ≤ result)⌝⦄ := by
  simp [numpy_max]
  apply And.intro
  · obtain ⟨x, hx_mem, hx_eq⟩ := max_in_foldl (l := a.toList) (init := a.get 0)
    cases hx_mem with
    | inl h_init =>
      exact ⟨0, h_init.symm.trans hx_eq⟩
    | inr h_in =>
      have : ∃ i : Fin (n + 1), a.get i = x := by
        rw [Vector.toList_get] at h_in
        obtain ⟨i, hi⟩ := List.mem_iff_get.mp h_in
        exact ⟨i, hi.symm⟩
      obtain ⟨i, hi⟩ := this
      exact ⟨i, hi.trans hx_eq⟩
  · intro i
    have h_in : a.get i ∈ a.toList := vector_get_in_toList
    exact foldl_max_ge h_in