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
lemma foldl_min_mem (l : List Float) (x : Float) : x ∈ l → l.foldl min x ≤ x := by
  intro h
  induction l generalizing x with
  | nil => simp
  | cons head tail ih =>
    simp [List.foldl]
    apply ih
    simp

-- LLM HELPER
lemma foldl_min_le_all (l : List Float) (x : Float) : ∀ y ∈ l, l.foldl min x ≤ y := by
  intro y hy
  induction l generalizing x with
  | nil => simp at hy
  | cons head tail ih =>
    simp [List.foldl]
    cases hy with
    | inl h => 
      rw [h]
      apply le_min_left
    | inr h =>
      apply ih
      exact h

-- LLM HELPER
lemma vector_get_mem (a : Vector Float (n + 1)) (i : Fin (n + 1)) : a.get i ∈ a.toList := by
  exact Vector.get_mem a i

-- LLM HELPER
lemma vector_get_zero_mem (a : Vector Float (n + 1)) : a.get 0 ∈ a.toList := by
  exact vector_get_mem a 0

-- LLM HELPER
lemma foldl_min_achieves_minimum (l : List Float) (x : Float) : 
  ∃ y ∈ x :: l, l.foldl min x = y := by
  induction l generalizing x with
  | nil => 
    simp [List.foldl]
    exact ⟨x, List.mem_cons_self x [], rfl⟩
  | cons head tail ih =>
    simp [List.foldl]
    have := ih (min x head)
    cases this with
    | intro y hy =>
      cases hy with
      | intro hmem heq =>
        cases hmem with
        | inl h =>
          rw [h] at heq
          by_cases hc : x ≤ head
          · simp [min_def, hc] at heq
            exact ⟨x, List.mem_cons_self x (head :: tail), heq⟩
          · simp [min_def, hc] at heq
            exact ⟨head, List.mem_cons_of_mem x (List.mem_cons_self head tail), heq⟩
        | inr h =>
          exact ⟨y, List.mem_cons_of_mem x (List.mem_cons_of_mem head h), heq⟩

-- LLM HELPER
lemma foldl_min_is_min_of_nonempty (a : Vector Float (n + 1)) : 
  let result := a.toList.foldl min (a.get 0)
  (∃ i : Fin (n + 1), a.get i = result) ∧ (∀ i : Fin (n + 1), result ≤ a.get i) := by
  constructor
  · -- Existence part
    have h : ∃ y ∈ a.get 0 :: a.toList, a.toList.foldl min (a.get 0) = y := 
      foldl_min_achieves_minimum a.toList (a.get 0)
    cases h with
    | intro y hy =>
      cases hy with
      | intro hmem heq =>
        cases hmem with
        | inl h1 =>
          rw [h1] at heq
          exact ⟨0, heq.symm⟩
        | inr h2 =>
          have : ∃ i : Fin (n + 1), a.get i = y := by
            rw [← Vector.get_mem_iff_exists_get]
            exact h2
          cases this with
          | intro i hi =>
            rw [hi] at heq
            exact ⟨i, heq.symm⟩
  · -- For all part
    intro i
    have : a.get i ∈ a.toList := vector_get_mem a i
    exact foldl_min_le_all a.toList (a.get 0) (a.get i) this

/-- Specification: numpy.min returns the minimum element in the vector.

    Precondition: True (non-empty constraint is in the type)
    Postcondition: result is the minimum value and is an element of the vector
-/
theorem numpy_min_spec (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    numpy_min a
    ⦃⇓result => ⌜(∃ i : Fin (n + 1), a.get i = result) ∧
                (∀ i : Fin (n + 1), result ≤ a.get i)⌝⦄ := by
  apply Triple.pure
  intro h
  simp [numpy_min]
  exact foldl_min_is_min_of_nonempty a