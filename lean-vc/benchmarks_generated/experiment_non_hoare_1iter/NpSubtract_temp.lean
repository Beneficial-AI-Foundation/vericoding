/-
# NumPy Subtract Specification

Port of np_substract.dfy to Lean 4
-/

namespace DafnySpecs.NpSubtract

/-- Element-wise subtraction of two vectors -/
def subtract {n : Nat} (a b : Vector Int n) : Vector Int n := 
  Vector.zipWith (· - ·) a b

/-- Specification: The result has the same length as inputs -/
theorem subtract_length {n : Nat} (a b : Vector Int n) :
  (subtract a b).toList.length = n := by
  simp [subtract]
  exact Vector.toList_length _

/-- Specification: Each element is the difference of corresponding input elements -/
theorem subtract_spec {n : Nat} (a b : Vector Int n) :
  ∀ i : Fin n, (subtract a b)[i] = a[i] - b[i] := by
  intro i
  simp [subtract]
  exact Vector.zipWith_get _ _ _ _

end DafnySpecs.NpSubtract