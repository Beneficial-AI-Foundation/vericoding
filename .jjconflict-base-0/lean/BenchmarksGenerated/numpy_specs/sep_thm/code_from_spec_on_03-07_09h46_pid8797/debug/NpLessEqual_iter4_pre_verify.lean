/-
# NumPy Less Equal Specification

Port of np_less_equal.dfy to Lean 4
-/

namespace DafnySpecs.NpLessEqual

/-- Element-wise less than or equal comparison of two vectors -/
def lessEqual {n : Nat} (a b : Vector Int n) : Vector Bool n := 
  Vector.ofFn (fun i => a[i] ≤ b[i])

/-- Specification: The result has the same length as inputs -/
theorem lessEqual_length {n : Nat} (a b : Vector Int n) :
  (lessEqual a b).toList.length = n := by
  simp [lessEqual, Vector.toList_ofFn, List.length_ofFn]

/-- Specification: Each element is true iff corresponding element in a is <= element in b -/
theorem lessEqual_spec {n : Nat} (a b : Vector Int n) :
  ∀ i : Fin n, (lessEqual a b)[i] = (a[i] ≤ b[i]) := by
  intro i
  simp [lessEqual, Vector.get_ofFn]

end DafnySpecs.NpLessEqual