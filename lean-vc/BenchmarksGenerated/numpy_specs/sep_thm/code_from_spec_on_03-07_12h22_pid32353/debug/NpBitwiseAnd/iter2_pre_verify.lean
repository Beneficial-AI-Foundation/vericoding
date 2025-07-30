/-
# NumPy Bitwise And Specification

Port of np_bitwise_and.dfy to Lean 4
-/

namespace DafnySpecs.NpBitwiseAnd

/-- Element-wise bitwise AND of two vectors -/
def bitwiseAnd {n : Nat} (a b : Vector Nat n) : Vector Nat n := 
  Vector.ofFn (fun i => a[i] &&& b[i])

/-- Specification: The result has the same length as inputs -/
theorem bitwiseAnd_length {n : Nat} (a b : Vector Nat n) :
  (bitwiseAnd a b).toList.length = n := by
  simp [bitwiseAnd, Vector.toList_ofFn]

/-- Specification: Each element is the bitwise AND of corresponding input elements -/
theorem bitwiseAnd_spec {n : Nat} (a b : Vector Nat n) :
  ∀ i : Fin n, (bitwiseAnd a b)[i] = a[i] &&& b[i] := by
  intro i
  simp [bitwiseAnd]
  rfl

end DafnySpecs.NpBitwiseAnd