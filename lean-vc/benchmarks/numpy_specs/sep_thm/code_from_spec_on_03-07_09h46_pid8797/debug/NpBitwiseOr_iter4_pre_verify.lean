/-
# NumPy Bitwise Or Specification

Port of np_bitwise_or.dfy to Lean 4
-/

namespace DafnySpecs.NpBitwiseOr

/-- Element-wise bitwise OR of two vectors -/
def bitwiseOr {n : Nat} (a b : Vector Nat n) : Vector Nat n := 
  Vector.ofFn (fun i => a[i] ||| b[i])

/-- Specification: The result has the same length as inputs -/
theorem bitwiseOr_length {n : Nat} (a b : Vector Nat n) :
  (bitwiseOr a b).toList.length = n := by
  simp [bitwiseOr, Vector.toList_ofFn]

/-- Specification: Each element is the bitwise OR of corresponding input elements -/
theorem bitwiseOr_spec {n : Nat} (a b : Vector Nat n) :
  ∀ i : Fin n, (bitwiseOr a b)[i] = a[i] ||| b[i] := by
  intro i
  simp [bitwiseOr, Vector.get_ofFn]

end DafnySpecs.NpBitwiseOr