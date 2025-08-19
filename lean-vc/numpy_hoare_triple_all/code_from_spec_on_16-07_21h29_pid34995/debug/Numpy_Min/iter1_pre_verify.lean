import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.min: Minimum value in array.

    Returns the minimum value among all elements in the array.
    Requires a non-empty array since there is no minimum of an empty set.

    This is a reduction operation that finds the smallest value in the array.
-/
def numpy_min (a : Vector Float (n + 1)) : Id Float :=
  Id.pure (a.toList.foldl min (a.get 0))

-- LLM HELPER
lemma foldl_min_mem (l : List Float) (x : Float) : x ∈ l → l.foldl min x ≤ x := by
  intro h
  simp [List.foldl_le_of_le_init]

-- LLM HELPER
lemma foldl_min_le_all (l : List Float) (x : Float) : ∀ y ∈ l, l.foldl min x ≤ y := by
  intro y hy
  simp [List.foldl_le_of_mem, hy]

-- LLM HELPER
lemma foldl_min_exists (l : List Float) (x : Float) : x ∈ l → ∃ y ∈ x :: l, l.foldl min x = y := by
  intro h
  cases' List.mem_foldl_min h with h1 h2
  · exact ⟨x, List.mem_cons_self x l, h1⟩
  · exact ⟨l.foldl min x, List.mem_cons_of_mem x h2, rfl⟩

-- LLM HELPER
lemma vector_get_mem (a : Vector Float (n + 1)) (i : Fin (n + 1)) : a.get i ∈ a.toList := by
  exact Vector.get_mem a i

-- LLM HELPER
lemma vector_get_zero_mem (a : Vector Float (n + 1)) : a.get 0 ∈ a.toList := by
  exact vector_get_mem a 0

-- LLM HELPER
lemma foldl_min_is_min_of_nonempty (a : Vector Float (n + 1)) : 
  let result := a.toList.foldl min (a.get 0)
  (∃ i : Fin (n + 1), a.get i = result) ∧ (∀ i : Fin (n + 1), result ≤ a.get i) := by
  constructor
  · -- Existence part
    have h : ∃ y ∈ a.get 0 :: a.toList, a.toList.foldl min (a.get 0) = y := by
      apply foldl_min_exists
      exact vector_get_zero_mem a
    simp at h
    cases' h with y hy
    cases' hy with hmem heq
    cases' hmem with h1 h2
    · -- y = a.get 0
      rw [h1] at heq
      exact ⟨0, heq.symm⟩
    · -- y ∈ a.toList
      have : ∃ i : Fin (n + 1), a.get i = y := by
        rw [← Vector.get_mem_iff_exists_get]
        exact h2
      cases' this with i hi
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
  apply pure_spec
  intro h
  simp [numpy_min]
  exact foldl_min_is_min_of_nonempty a