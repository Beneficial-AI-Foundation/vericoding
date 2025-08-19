/-
# NumPy Not Equal Specification

Port of np_not_equal.dfy to Lean 4
-/

namespace DafnySpecs.NpNotEqual

/-- Element-wise inequality comparison of two vectors -/
def notEqual {n : Nat} (a b : Vector Int n) : Vector Bool n := 
  Vector.ofFn (fun i => a[i] ≠ b[i])

/-- LLM HELPER -/
lemma vector_ofFn_length {n : Nat} (f : Fin n → Bool) :
  (Vector.ofFn f).toList.length = n := by
  simp [Vector.ofFn]

/-- Specification: The result has the same length as inputs -/
theorem notEqual_length {n : Nat} (a b : Vector Int n) :
  (notEqual a b).toList.length = n := by
  unfold notEqual
  exact vector_ofFn_length (fun i => a[i] ≠ b[i])

/-- Specification: Each element is true iff corresponding input elements are not equal -/
theorem notEqual_spec {n : Nat} (a b : Vector Int n) :
  ∀ i : Fin n, (notEqual a b)[i] = (a[i] ≠ b[i]) := by
  intro i
  unfold notEqual
  simp [Vector.ofFn]

end DafnySpecs.NpNotEqual