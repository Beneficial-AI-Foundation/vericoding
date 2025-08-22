/-
# NumPy Greater Equal Specification

Port of np_greater_equal.dfy to Lean 4
-/

namespace DafnySpecs.NpGreaterEqual

/-- Element-wise greater than or equal comparison of two vectors -/
def greaterEqual {n : Nat} (a b : Vector Int n) : Vector Bool n := 
  Vector.ofFn (fun i => a[i] ≥ b[i])

/-- Specification: The result has the same length as inputs -/
theorem greaterEqual_length {n : Nat} (a b : Vector Int n) :
  (greaterEqual a b).toList.length = n := by
  simp [greaterEqual]
  exact Vector.length_toList _

/-- Specification: Each element is true iff corresponding element in a is >= element in b -/
theorem greaterEqual_spec {n : Nat} (a b : Vector Int n) :
  ∀ i : Fin n, (greaterEqual a b)[i] = (a[i] ≥ b[i]) := by
  intro i
  simp [greaterEqual]
  exact Vector.get_ofFn _ _

end DafnySpecs.NpGreaterEqual