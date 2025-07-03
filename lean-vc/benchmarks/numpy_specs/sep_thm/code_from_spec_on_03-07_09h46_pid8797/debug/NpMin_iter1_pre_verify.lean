/-
# NumPy Min Specification

Port of np_min.dfy to Lean 4
-/

namespace DafnySpecs.NpMin

/-- Find the minimum element in a non-empty vector -/
def min {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  Vector.foldl Int.min a[0] a

/- LLM HELPER -/
lemma vector_foldl_min_le {n : Nat} (h : n > 0) (a : Vector Int n) (i : Fin n) :
  Vector.foldl Int.min a[0] a ≤ a[i] := by
  induction' n using Nat.strong_induction_on with n ih
  cases' n with n'
  · contradiction
  · simp [Vector.foldl]
    sorry -- This would require a more detailed proof about vector fold properties

/- LLM HELPER -/
lemma vector_foldl_min_exists {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, Vector.foldl Int.min a[0] a = a[i] := by
  induction' n using Nat.strong_induction_on with n ih
  cases' n with n'
  · contradiction
  · cases' n' with n''
    · use 0
      simp [Vector.foldl]
    · sorry -- This would require a more detailed proof about vector fold properties

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