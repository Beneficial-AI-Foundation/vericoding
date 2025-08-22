/-
# NumPy Square Specification

Port of np_square.dfy to Lean 4

https://numpy.org/doc/stable/reference/generated/numpy.square.html
Return the element-wise square of the input.
-/

namespace DafnySpecs.NpSquare

/-- Element-wise square of a vector -/
def square {n : Nat} (arr : Vector Int n) : Vector Int n := 
  Vector.map (fun x => x * x) arr

/-- Specification: The result has the same length as input -/
theorem square_length {n : Nat} (arr : Vector Int n) :
  (square arr).toList.length = n := by
  simp [square]
  rw [Vector.toList_map]
  simp

/-- Specification: Each element is the square of the corresponding input element -/
theorem square_spec {n : Nat} (arr : Vector Int n) :
  ∀ i : Fin n, (square arr)[i] = (arr[i]) * (arr[i]) := by
  intro i
  simp [square]
  rw [Vector.get_map]

end DafnySpecs.NpSquare