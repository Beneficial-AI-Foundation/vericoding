/-
# NumPy Multiply Specification

Port of np_multiply.dfy to Lean 4
-/

namespace DafnySpecs.NpMultiply

/-- Element-wise multiplication of two vectors -/
def multiply {n : Nat} (a b : Vector Int n) : Vector Int n := 
  ⟨(List.zipWith (· * ·) a.toList b.toList).toArray, by simp [List.length_zipWith, Vector.length_toList]⟩

/-- Specification: The result has the same length as inputs -/
theorem multiply_length {n : Nat} (a b : Vector Int n) :
  (multiply a b).toList.length = n := by
  simp [multiply, List.length_zipWith, Vector.length_toList]

/-- Specification: Each element is the product of corresponding input elements -/
theorem multiply_spec {n : Nat} (a b : Vector Int n) :
  ∀ i : Fin n, (multiply a b)[i] = a[i] * b[i] := by
  intro i
  simp [multiply, Vector.get_mk, Array.get_toArray, List.get_zipWith]

end DafnySpecs.NpMultiply