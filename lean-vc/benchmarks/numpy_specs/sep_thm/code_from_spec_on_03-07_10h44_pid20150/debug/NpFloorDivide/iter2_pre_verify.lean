/-
# NumPy Floor Divide Specification

Port of np_floor_divide.dfy to Lean 4
-/

namespace DafnySpecs.NpFloorDivide

/-- Type constraint ensuring all elements are non-zero -/
def NonZeroVector (n : Nat) := { v : Vector Int n // ∀ i : Fin n, v[i] ≠ 0 }

/-- Element-wise floor division of two vectors -/
def floorDivide {n : Nat} (a : Vector Int n) (b : NonZeroVector n) : Vector Int n := 
  Vector.ofFn (fun i => a[i] / b.val[i])

/-- Specification: The result has the same length as inputs -/
theorem floorDivide_length {n : Nat} (a : Vector Int n) (b : NonZeroVector n) :
  (floorDivide a b).toList.length = n := by
  simp [floorDivide, Vector.toList_ofFn]

/-- Specification: Each element is the floor division of corresponding input elements -/
theorem floorDivide_spec {n : Nat} (a : Vector Int n) (b : NonZeroVector n) :
  ∀ i : Fin n, (floorDivide a b)[i] = a[i] / (b.val[i]) := by
  intro i
  simp [floorDivide]
  rw [Vector.get_ofFn]

end DafnySpecs.NpFloorDivide