/-
# NumPy Subtract Specification

Port of np_substract.dfy to Lean 4
-/

namespace DafnySpecs.NpSubtract

-- LLM HELPER
def subtract_array {n : Nat} (a b : Vector Int n) : Array Int :=
  Array.zipWith (· - ·) a.toArray b.toArray

-- LLM HELPER
theorem subtract_array_size {n : Nat} (a b : Vector Int n) :
  (subtract_array a b).size = n := by
  simp [subtract_array]
  rw [Array.size_zipWith]
  simp [Vector.toArray_size]

/-- Element-wise subtraction of two vectors -/
def subtract {n : Nat} (a b : Vector Int n) : Vector Int n := 
  Vector.mk (subtract_array a b) (subtract_array_size a b)

/-- Specification: The result has the same length as inputs -/
theorem subtract_length {n : Nat} (a b : Vector Int n) :
  (subtract a b).toList.length = n := by
  simp [subtract]
  rw [Vector.length_toList]

/-- Specification: Each element is the difference of corresponding input elements -/
theorem subtract_spec {n : Nat} (a b : Vector Int n) :
  ∀ i : Fin n, (subtract a b)[i] = a[i] - b[i] := by
  intro i
  simp [subtract]
  rw [Vector.getElem_mk]
  rw [Array.getElem_zipWith]
  simp [Vector.toArray_size]

end DafnySpecs.NpSubtract