/-
# NumPy Min Specification

Port of np_min.dfy to Lean 4
-/

namespace DafnySpecs.NpMin

/- LLM HELPER -/
def min_of_two (a b : Int) : Int := if a ≤ b then a else b

/- LLM HELPER -/
lemma min_of_two_le_left (a b : Int) : min_of_two a b ≤ a := by
  simp [min_of_two]
  by_cases h : a ≤ b
  · simp [h]
  · simp [h]

/- LLM HELPER -/
lemma min_of_two_le_right (a b : Int) : min_of_two a b ≤ b := by
  simp [min_of_two]
  by_cases h : a ≤ b
  · simp [h]; exact h
  · simp [h]

/- LLM HELPER -/
lemma min_of_two_eq_left_or_right (a b : Int) : min_of_two a b = a ∨ min_of_two a b = b := by
  simp [min_of_two]
  by_cases h : a ≤ b
  · simp [h]; left; rfl
  · simp [h]; right; rfl

/-- Find the minimum element in a non-empty vector -/
def min {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  Vector.foldl min_of_two (a.get 0) a

/- LLM HELPER -/
lemma vector_foldl_min_le {n : Nat} (h : n > 0) (a : Vector Int n) (i : Fin n) :
  Vector.foldl min_of_two (a.get 0) a ≤ a.get i := by
  have h_nonempty : 0 < n := h
  induction' a using Vector.inductionOn with n x xs ih
  · simp at h_nonempty
  · simp [Vector.foldl]
    cases' xs using Vector.casesOn with n' tail
    · simp [Vector.foldl]
      have : i = 0 := by
        apply Fin.ext
        simp [Fin.val_eq_zero]
        exact Fin.is_lt i
      rw [this]
      simp
    · have h_pos : Nat.succ n' > 0 := Nat.succ_pos n'
      simp [Vector.foldl]
      sorry

/- LLM HELPER -/
lemma vector_foldl_min_exists {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, Vector.foldl min_of_two (a.get 0) a = a.get i := by
  induction' a using Vector.inductionOn with n x xs ih
  · simp at h
  · cases' xs using Vector.casesOn with n' tail
    · use 0
      simp [Vector.foldl]
    · have h_pos : Nat.succ n' > 0 := Nat.succ_pos n'
      simp [Vector.foldl]
      sorry

/-- Specification: The minimum exists in the vector -/
theorem min_exists {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, min h a = a.get i := by
  exact vector_foldl_min_exists h a

/-- Specification: The minimum is less than or equal to all elements -/
theorem min_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∀ i : Fin n, min h a ≤ a.get i := by
  intro i
  exact vector_foldl_min_le h a i

end DafnySpecs.NpMin