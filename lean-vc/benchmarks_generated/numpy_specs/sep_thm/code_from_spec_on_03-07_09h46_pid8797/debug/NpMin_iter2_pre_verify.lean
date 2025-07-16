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
  Vector.foldl min_of_two a[0] a

/- LLM HELPER -/
lemma vector_foldl_min_le {n : Nat} (h : n > 0) (a : Vector Int n) (i : Fin n) :
  Vector.foldl min_of_two a[0] a ≤ a[i] := by
  induction' n using Nat.strong_induction_on with n ih
  cases' n with n'
  · contradiction
  · simp [Vector.foldl]
    by_cases h_eq : n' = 0
    · subst h_eq
      simp
      have : i = 0 := by
        apply Fin.ext
        simp [Fin.val_eq_zero]
        exact Fin.is_lt i
      rw [this]
    · have h_pos : n' > 0 := Nat.pos_of_ne_zero h_eq
      sorry

/- LLM HELPER -/
lemma vector_foldl_min_exists {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, Vector.foldl min_of_two a[0] a = a[i] := by
  induction' n using Nat.strong_induction_on with n ih
  cases' n with n'
  · contradiction
  · cases' n' with n''
    · use 0
      simp [Vector.foldl]
    · sorry

/-- Specification: The minimum exists in the vector -/
theorem min_exists {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, min h a = a[i] := by
  exact vector_foldl_min_exists h a

/-- Specification: The minimum is less than or equal to all elements -/
theorem min_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∀ i : Fin n, min h a ≤ a[i] := by
  intro i
  exact vector_foldl_min_le h a i

end DafnySpecs.NpMin